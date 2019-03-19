import ProofNode, {Kind} from '../../../key/prooftree/ProofNode';

export default class DisplayTreeNode {

  public collapsed: boolean;
  public selected: boolean;
  public text: string;
  public children: DisplayTreeNode[];
  public kind: Kind;
  public sequent: string;
  public serialNr: number;
  public oneStepId: number;

  public constructor(
    collapsed: boolean,
    selected: boolean,
    text: string,
    children: DisplayTreeNode[],
    kind: Kind,
    sequent: string,
    serialNr: number,
    oneStepId: number
  ) {
    this.collapsed = collapsed;
    this.selected = selected;
    this.text = text;
    this.children = children;
    this.kind = kind;
    this.sequent = sequent;
    this.serialNr = serialNr;
    this.oneStepId = oneStepId;
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
}

export function toDisplayTree(tree: ProofNode): DisplayTreeNode | null{
  if(tree === null) return null;
  let children: DisplayTreeNode[] = [];

  for(let child of tree.children){
    let parsedChild: DisplayTreeNode | null = toDisplayTree(child);
    if(parsedChild != null)
      children.push(parsedChild);
  }

  let collapsed: boolean = children.length > 1;

  return new DisplayTreeNode(
    collapsed,
    false,
    tree.text,
    children,
    tree.kind,
    tree.sequent,
    tree.serialNr,
    tree.oneStepId
  );
}
