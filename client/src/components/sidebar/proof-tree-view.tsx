import React from 'react';
import {Kind} from '../../key/prooftree/ProofNode';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofResults from '../../key/netdata/ProofResults';

import DisplayTreeNode, {toDisplayTree} from './displaytree/displaytreenode';

import ObligationResult from '../../key/netdata/ObligationResult';

export default class ProofTreeView extends React.Component<Props, State> {

  public selectedPath: DisplayTreeNode[] = [];
  public lastSelected: DisplayTreeNode | null = null;

  constructor(props: Props) {
    super(props);
    
    this.selectNode = this.selectNode.bind(this);
    this.handleKeydown = this.handleKeydown.bind(this);
    this.collapseNode = this.collapseNode.bind(this);
    this.state = {
      displayTrees: [],
      changed: false,
    };
  }

  public collapseNode(node: DisplayTreeNode){
    node.collapsed = !node.collapsed;
    this.setState({
      changed:true
    });
  }

  public selectNode(path: DisplayTreeNode[]){
    let node: DisplayTreeNode = path[path.length - 1];
    let previousSelected: DisplayTreeNode = this.selectedPath[this.selectedPath.length - 1];
    if(previousSelected)
      previousSelected.selected = false;
    if(node)
      node.selected = true;
    this.lastSelected = node;
    this.selectedPath = path;
    this.setState({
      changed:true
    });
  }

  public shouldComponentUpdate(nextProps: Props, nextState: State): boolean {
    // only do a shallow comparison, so that the proof tree view is not constantly updated.

    if(nextState.changed){
      this.setState({
        changed: false,
      })
      return true;
    } else{
      return this.props.displaySequent !== nextProps.displaySequent
      || this.props.proofResults !== nextProps.proofResults
    }
  }

  public findNextLeafUp(node: DisplayTreeNode): DisplayTreeNode|null{
      let numberOfChildren: number = node.children.length;
      if(numberOfChildren == 0 || node.kind === Kind.OneStepSimplification){
        
        newSelectedNode.push(node.children[numberOfChildren - 1]);
      }else{
        if(node.children[numberOfChildren - 1].collapsed != true){
            newSelectedNode.push(node.children[numberOfChildren - 1]);
            this.findNextLeafUp(node.children[numberOfChildren - 1], newSelectedNode);
        }
      } 
  }

  public handleKeydown(event: any){
      
        let newSelectedNode = this.selectedPath.slice();
        let leafNode: DisplayTreeNode = newSelectedNode[newSelectedNode.length - 1];
        console.log(leafNode);
        switch(event.keyCode){
          case 38:
              console.log("Up");
              console.log(newSelectedNode[newSelectedNode.length - 1].serialNr);
              if(newSelectedNode.length > 1){  //We are not in the root node
                  let parentNode: DisplayTreeNode = newSelectedNode[newSelectedNode.length - 2];
                  let index: number = parentNode.getIndex(leafNode);
                  
                  console.log('Index within the children array of the parent before update:' + index);
                  newSelectedNode.pop();
                  if(index > 0){
                    let nextNodeUp: DisplayTreeNode = newSelectedNode[newSelectedNode.length - 1].children[index - 1];
                    this.findNextLeafUp(nextNodeUp, newSelectedNode);
//                    if(nextNodeUp.collapsed || nextNodeUp.children.length == 0 || (nextNodeUp.children.length != 0 && nextNodeUp.children[0].kind === Kind.OneStepSimplification)){
//                        newSelectedNode.push(nextNodeUp);
//                    }else{
//                        let nextNodeUpChildIndex = nextNodeUp.children.length - 1; 
//                        newSelectedNode.push(nextNodeUp);
//                        newSelectedNode.push(nextNodeUp.children[nextNodeUpChildIndex]);
//                    }
                  }
              }
              break;
          case 40:
              // Down
              if((leafNode.collapsed || leafNode.children.length == 0)&& newSelectedNode.length > 1){
                  let parentNode: DisplayTreeNode = newSelectedNode[newSelectedNode.length - 2];
                  let index: number = parentNode.getIndex(leafNode);
                  console.log(parentNode.children.length);
                  if(index < parentNode.children.length - 1){ 
                        newSelectedNode.pop();
                        newSelectedNode.push(parentNode.children[index + 1]);
                  }else{
                     if(newSelectedNode.length > 2){
                        let GrandParentNode: DisplayTreeNode = newSelectedNode[newSelectedNode.length - 3];
                        let GrandParentNodeChildIndex: number = GrandParentNode.getIndex(parentNode);
                        if(GrandParentNodeChildIndex !== GrandParentNode.children.length - 1){
                            newSelectedNode.pop();
                            newSelectedNode.pop();
                            newSelectedNode.push(GrandParentNode.children[GrandParentNodeChildIndex + 1]);
                        }
                     } 
                  }
              } else {
                  if(leafNode.children.length > 0){
                    newSelectedNode.push(leafNode.children[0]);
                  }
              }
              break;
          case 39:
              // Right
              newSelectedNode[newSelectedNode.length - 1].collapsed = false;
              break;
          case 37:
              // Left
              newSelectedNode[newSelectedNode.length - 1].collapsed = true;
              break;
        }

        if(event.keyCode == 37 || event.keyCode == 39 || event.keyCode == 40 || event.keyCode == 38){ 
          this.props.displaySequent(newSelectedNode[newSelectedNode.length -1].sequent);   
          this.selectNode(newSelectedNode);
        }
    } 

  componentDidMount() {
      document.addEventListener("keydown", this.handleKeydown);
  }

  componentWillUnmount() {
      document.removeEventListener("keydown", this.handleKeydown);
  }

  componentDidUpdate(prevProps: Props){
    if(prevProps.proofResults !== this.props.proofResults){
      let results = this.props.proofResults;
      let displayTrees: DisplayTreeNode[] = [];
      if (results != null) {
        displayTrees =
          results.succeeded
            .concat(results.failed)
            .concat(results.errors)
            .map((result: ObligationResult) => result.proofTree)
            .map(proofTree => toDisplayTree(proofTree, null))
            .filter((proofTree: DisplayTreeNode | null): proofTree is DisplayTreeNode => proofTree != null);

      this.setState({
        displayTrees: displayTrees,
        changed: true
      });
      }
    }
  }

  public render() {
    console.log("rendering proof trees"); 
    // TODO better keys
    let nodes: DisplayTreeNode[] = this.state.displayTrees;
    if (nodes.length > 0) {
      return (
        <div>
          {
            nodes.map(node => (
                <GuiProofNode
                  key={`${node.serialNr},${node.oneStepId}`}
                  // TODO better keys
                  node={node}
                  displaySequent={this.props.displaySequent}
                  selectNode={this.selectNode}
                  collapseNode={this.collapseNode}
                  path={[node]}
                />
                )
            )
          }
        </div>
      );
    } else {
      return <>No open proof.</>;
    }
  }
}

// defining the structure of this react components properties
interface Props {
  proofResults: ProofResults;
  displaySequent: (sequent: string) => void;
}

interface State {
  displayTrees: DisplayTreeNode[];
  changed: boolean;
}
