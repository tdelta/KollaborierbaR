import ProofNode, { Kind } from '../../../key/prooftree/ProofNode';
import React, { RefObject } from 'react';
import GuiProofNode from '../gui-proof-node';

/**
 * View model of an proof tree.
 * Its main purpose is to provide helper functions for navigating the tree
 * (for example if the user moves through the tree using arrow keys.)
 */
export default class DisplayTreeNode {
  public collapsed: boolean;
  public selected: boolean;
  public text: string;
  public children: DisplayTreeNode[] = [];
  public kind: Kind;
  public sequent: string;
  public serialNr: number;
  public oneStepId: number;
  public parent: DisplayTreeNode | null;
  public ref: RefObject<GuiProofNode>;

  public constructor(
    collapsed: boolean,
    selected: boolean,
    text: string,
    kind: Kind,
    sequent: string,
    serialNr: number,
    oneStepId: number,
    parent: DisplayTreeNode | null
  ) {
    this.collapsed = collapsed;
    this.selected = selected;
    this.text = text;
    this.kind = kind;
    this.sequent = sequent;
    this.serialNr = serialNr;
    this.oneStepId = oneStepId;
    this.parent = parent;
    this.ref = React.createRef();

    this.getRef = this.getRef.bind(this);
  }

  /*
   *  Find the array index of the node in the child array of its parent
   *  @returns number representing position in the child array
   */
  public getIndex(node: DisplayTreeNode): number {
    return this.children.findIndex(child => {
      return node.serialNr === child.serialNr;
    });
  }

  public setChildren(node: DisplayTreeNode[]) {
    this.children = node;
  }

  public getRef(): RefObject<GuiProofNode> {
    return this.ref;
  }
  /*
   *  Finds and returns the next visible leaf with the highest position in the tree order
   *  @returns found DisplayTreeNode if non found return this
   */
  public findNextLeafUp(): DisplayTreeNode {
    const numberOfChildren: number = this.children.length;
    console.log(this.kind);
    if (numberOfChildren === 0 || this.collapsed) {
      return this;
    } else {
      if (this.children[0].kind === Kind.OneStepSimplification) {
        return this;
      } else {
        if (this.children[numberOfChildren - 1].collapsed) {
          return this.children[numberOfChildren - 1];
        } else {
          return this.children[numberOfChildren - 1].findNextLeafUp();
        }
      }
    }
  }

  /*
   *  Findes and reutrn the next visible leaf with the lowest position in the tree order
   *  @returns found DisplayTreeNode if it exists else null
   */
  public findNextLeafDown(): DisplayTreeNode | null {
    if (this.parent != null) {
      // am i last ?
      const index: number = this.parent.getIndex(this);
      if (index < this.parent.children.length - 1) {
        return this.parent.children[index + 1];
      } else {
        return this.parent.findNextLeafDown();
      }
    } else {
      return null;
    }
  }
}

/*
 * Converts a given ProofNode into a DisplayTreeNode recursivly while including its parent
 *  @param ProofNode tree the given ProofNode
 *  @param DisplayTreeNode parent parent of the node
 *  @returns converte DisplayTreeNode from ProofNode
 */

export function toDisplayTree(
  tree: ProofNode,
  parent: DisplayTreeNode | null
): DisplayTreeNode | null {
  if (tree === null) return null;

  const collapsed: boolean = tree.children.length > 1;

  const result: DisplayTreeNode = new DisplayTreeNode(
    collapsed,
    false,
    tree.text,
    tree.kind,
    tree.sequent,
    tree.serialNr,
    tree.oneStepId,
    parent
  );

  const children: DisplayTreeNode[] = [];

  for (const child of tree.children) {
    const parsedChild: DisplayTreeNode | null = toDisplayTree(child, result);
    if (parsedChild != null) children.push(parsedChild);
  }

  result.setChildren(children);
  return result;
}
