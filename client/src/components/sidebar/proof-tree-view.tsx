import React from 'react';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofResults from '../../key/netdata/ProofResults';

import ObligationResult from '../../key/netdata/ObligationResult';

export default class ProofTreeView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.selectNode = this.selectNode.bind(this);
    this.handleKeydown = this.handleKeydown.bind(this);
    this.state = {
      selectedNode: []
    };
  }

  public selectNode(node: ProofNode[]){
    this.setState({
      selectedNode: node
    });
  }

  public shouldComponentUpdate(nextProps: Props, nextState: State): boolean {
    // only do a shallow comparison, so that the proof tree view is not constantly updated.

    return this.props.displaySequent !== nextProps.displaySequent
        || this.props.proofResults !== nextProps.proofResults
        || this.state.selectedNode !== nextState.selectedNode;
  }

  public handleKeydown(event: any){
        let serialNr = this.state.selectedNode[this.state.selectedNode.length - 1].serialNr;
        switch(event.keyCode){
          case 38:
              console.log("Up");
              console.log(this.state.selectedNode[this.state.selectedNode.length - 1].serialNr);
              if(this.state.selectedNode.length > 1){
                  if(this.state.selectedNode[this.state.selectedNode.length - 2].children.length > 0
                  && serialNr < this.state.selectedNode[this.state.selectedNode.length - 2].children.length){
                      if(serialNr === 0){
                        this.state.selectedNode.pop();
                      }else{
                        this.state.selectedNode.pop(); 
                        this.state.selectedNode.push(this.state.selectedNode.length - 2].children[serialNr - 1]);
                      } 
                  }
              }
              break;
          case 40:
              console.log("Down");
              break;
          case 39:
              console.log("Right");
              if(this.state.selectedNode[this.state.selectedNode.length - 1].children.length !== 0){
                  this.state.selectedNode.push(this.state.selectedNode[this.state.selectedNode.length - 1].children[0]);
              }
              break;
          case 37:
              console.log("Left");
              if(this.state.selectedNode.length !== 1){
                  this.state.selectedNode.pop();
              }
              break;
        } 
        console.log(this.state.selectedNode[this.state.selectedNode.length - 1]);        
    } 

  componentDidMount() {
      document.addEventListener("keydown", this.handleKeydown);
  }

  componentWillUnmount() {
      document.removeEventListener("keydown", this.handleKeydown);
  }

  public render() {
    let nodes: ProofNode[] = [];
    
    const results = this.props.proofResults;
    console.log("RESULTS");
    console.log(results);
    if (results != null) {
      nodes =
        results.succeeded
          .concat(results.failed)
          .concat(results.errors)
          .map((result: ObligationResult) => result.proofTree)
          .filter((proofTree: ProofNode) => proofTree != null);
    }
      
    // TODO better keys

    if (nodes.length > 0) {
      return (
        <div>
          {
            nodes.map(node => (
                <GuiProofNode
                  key={`${node.serialNr},${node.oneStepId}`}
                  // TODO better keys
                  node={node}
                  initiallyCollapsed={nodes.length > 1}
                  displaySequent={this.props.displaySequent}
                  selectNode={this.selectNode}
                  selectedNode={this.state.selectedNode}
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
  selectedNode: ProofNode[];
}
