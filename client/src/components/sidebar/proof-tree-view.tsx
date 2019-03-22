import React from 'react';
import {Kind} from '../../key/prooftree/ProofNode';

import ReactDOM from 'react-dom';

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

  public selectNode(node: DisplayTreeNode){
    this.props.displaySequent(node.sequent);
    console.log(node);

    //const tesNode = ReactDOM.findDOMNode(node.getRef());
    console.log(node.getRef());
      if(node.getRef() != null && node.getRef().current != null){
        const component : GuiProofNode = (node.getRef().current as GuiProofNode);
        const tesNode = (ReactDOM.findDOMNode(node.getRef().current) as Element);
        console.log(tesNode);
        if(tesNode!=null)
        tesNode.scrollIntoView();
      }
    //if(node != null && node.getRef() != null && node.getRef().current != null && node.getRef().current.offsetTop != null){
    //  window.scrollTo(0, node.getRef().current.offsetTop);
    //}
    if(this.lastSelected)
      this.lastSelected.selected = false;
    if(node)
      node.selected = true;
    this.lastSelected = node;
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

  

  public handleKeydown(event: any){
     if(this.lastSelected != null){ 
        let leafNode: DisplayTreeNode = this.lastSelected;
        console.log(leafNode);
        switch(event.keyCode){
          case 38:
              //Up
              if(leafNode.parent != null){  //We are not in the root node
                  let parentNode: DisplayTreeNode = leafNode.parent;
                  let index: number = parentNode.getIndex(leafNode);
                  if(index > 0){
                    this.selectNode(parentNode.children[index - 1].findNextLeafUp());
                  }else{
                    this.selectNode(parentNode)
                  }
              }
              break;
          case 40:
              // Down
              if(leafNode.collapsed == false && leafNode.children.length != 0 && leafNode.children[0].kind != Kind.OneStepSimplification){ 
                  this.selectNode(leafNode.children[0]);
                }else{
              if(leafNode.parent != null){
                let nextLeafDown: DisplayTreeNode|null = leafNode.findNextLeafDown();
                if(nextLeafDown != null){
                  this.selectNode(nextLeafDown);
                }
              }else{
                  
                  this.selectNode(leafNode);
                } 
              }
              break;
          case 39:
              // Right
              leafNode.collapsed = false;
              this.selectNode(leafNode);
              break;
          case 37:
              // Left
              leafNode.collapsed = true;
              this.selectNode(leafNode);
              break;
        }

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
                  ref={node.getRef()}
                  node={node}
                  selectNode={this.selectNode}
                  collapseNode={this.collapseNode}
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
