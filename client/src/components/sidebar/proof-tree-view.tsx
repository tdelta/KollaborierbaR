import React from 'react';
import {Kind} from '../../key/prooftree/ProofNode';

import ReactDOM from 'react-dom';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';

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
      displayNode: null,
      changed: false,
    };
  }

  /*
   * Invert collapsed boolean of given DisplayTreeNode
   * @param given node  
   */
  public collapseNode(node: DisplayTreeNode){
    node.collapsed = !node.collapsed;
    this.setState({
      changed:true
    });
  }

  /*
   * Marks the given DisplayTreeNode as selected
   * also scrolls selectNode into view
   * @param node given DisplayTreeNode
   */
  public selectNode(node: DisplayTreeNode){
    this.props.displaySequent(node.sequent);
    console.log(node);

    if(node.getRef().current != null){
      const component : GuiProofNode = (node.getRef().current as GuiProofNode);
      const element = (ReactDOM.findDOMNode(component) as Element);
      if(element!=null) {
        element.scrollIntoView({});
      }
    }
    if(this.lastSelected)
      this.lastSelected.selected = false;
    if(node)
      node.selected = true;
    this.lastSelected = node;
    this.setState({
      changed:true
    });
  }

  
/*
 * Eventhandler for arrow buttons to navigate the proof tree
 * @param event keyevent
 */
  public handleKeydown(event: any){
     if(this.lastSelected != null){ 
        let leafNode: DisplayTreeNode = this.lastSelected;
        console.log(leafNode);
        switch(event.keyCode){
          case 38:
              //Up
              if(leafNode.parent != null){  
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
    if(prevProps.obligationResult !== this.props.obligationResult){
      let displayNode: DisplayTreeNode | null = null;
      if (this.props.obligationResult != null) {
        displayNode = toDisplayTree(this.props.obligationResult.proofTree, null);
      }

      this.setState({
        changed: true,
        displayNode: displayNode
      });
    }
  }

  public render() {
    let node;
    let displayNode;

    if (this.props.obligationResult != null) {
      node = this.props.obligationResult.proofTree;
      displayNode = this.state.displayNode;
      // Reenable, if this behavior is desired:
      //initiallyCollapsed = this.props.obligationResult.kind === ObligationResultKind.success;
    }
    
    if (node != null && displayNode != null) {
      return (
        <div>
          <GuiProofNode
            key={`${node.serialNr},${node.oneStepId}`}
            ref={displayNode.getRef()}
            node={displayNode}
            selectNode={this.selectNode}
            collapseNode={this.collapseNode}
            proofTreeOperationInfo={this.props.proofTreeOperationInfo}
          />
        </div>
      );
    } else {
      return <>No open proof.</>;
    }
  }
}

// defining the structure of this react components properties
interface Props {
  obligationResult?: ObligationResult;
  displaySequent: (sequent: string) => void;
  proofTreeOperationInfo: { operation: () => void; label: string };
}

interface State {
  displayNode: DisplayTreeNode | null;
  changed: boolean;
}
