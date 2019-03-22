import ProofNode, {Kind} from '../../../key/prooftree/ProofNode';
import React, {RefObject} from 'react';
import GuiProofNode from '../gui-proof-node';

export default class DisplayTreeNode {

  public collapsed: boolean;
  public selected: boolean;
  public text: string;
  public children: DisplayTreeNode[] = [];
  public kind: Kind;
  public sequent: string;
  public serialNr: number;
  public oneStepId: number;
  public parent: DisplayTreeNode|null;
  public ref: RefObject<GuiProofNode>;

  public constructor(
    collapsed: boolean,
    selected: boolean,
    text: string,
    kind: Kind,
    sequent: string,
    serialNr: number,
    oneStepId: number,
    parent: DisplayTreeNode|null,
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

  public findNode(path: DisplayTreeNode[]): DisplayTreeNode | null{
    if(path.length === 1 &&
      this.serialNr === path[0].serialNr && this.oneStepId === path[0].oneStepId)
      return this;
    for(let child of this.children){
      let result: DisplayTreeNode | null = child.findNode(path.splice(0,1));
      if(result !== null) return result;
    }
    return null;
  }

  public getIndex(node: DisplayTreeNode){
    return this.children.findIndex(child=> {
       return node.serialNr === child.serialNr;
    });
  }

  public setChildren(node: DisplayTreeNode[]){
    this.children = node;
  }


  public getRef(): RefObject<GuiProofNode>{
    return this.ref;
  }

  //
  //
  public findNextLeafUp(): DisplayTreeNode{
      let numberOfChildren: number = this.children.length;
      console.log(this.kind);
      if(numberOfChildren == 0  || this.collapsed){
          return this;
      }else{
        if(this.children[0].kind === Kind.OneStepSimplification){
          return this; 
        }else{
          if(this.children[numberOfChildren - 1].collapsed){
            return this.children[numberOfChildren - 1];
          }else{
            return this.children[numberOfChildren - 1].findNextLeafUp();
        }
        }
      } 
  }

  public findNextLeafDown(): DisplayTreeNode| null{
        if(this.parent != null){
          // am i last ? 
          let index: number = this.parent.getIndex(this);
          if(index < this.parent.children.length - 1){
            return this.parent.children[index + 1];
          }else{
            return this.parent.findNextLeafDown();
          }
        }else{
          return null;        
       } 
  }
}



export function toDisplayTree(tree: ProofNode, parent: DisplayTreeNode|null): DisplayTreeNode | null{
  if(tree === null) return null;

 

  let collapsed: boolean = tree.children.length > 1;

  let result: DisplayTreeNode = new DisplayTreeNode(
    collapsed,
    false,
    tree.text,
    tree.kind,
    tree.sequent,
    tree.serialNr,
    tree.oneStepId,
    parent,
  );

  let children: DisplayTreeNode[] = [];   

 for(let child of tree.children){
    let parsedChild: DisplayTreeNode | null = toDisplayTree(child, result);
    if(parsedChild != null)
      children.push(parsedChild);
 }

  result.setChildren(children);
  return result;
}
