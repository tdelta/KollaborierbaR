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
      selectedNode: [],
      changed: false,
    };
  }

  public selectNode(node: ProofNode[]){
    this.setState({
      selectedNode: node
    });
  }

  public shouldComponentUpdate(nextProps: Props, nextState: State): boolean {
    // only do a shallow comparison, so that the proof tree view is not constantly updated.

    if(this.state.changed){
      this.setState({
        changed: false,
      })
      return true;
    } else{
      return this.props.displaySequent !== nextProps.displaySequent
      || this.props.proofResults !== nextProps.proofResults
      || this.state.selectedNode !== nextState.selectedNode;
    }
  }

  public handleKeydown(event: any){
        let newSelectedNode = this.state.selectedNode;
        this.setState({
          changed: true,
        })

        switch(event.keyCode){
          case 38:
              console.log("Up");
              console.log(newSelectedNode[newSelectedNode.length - 1].serialNr);
              if(newSelectedNode.length > 1){
                  let foundUp = newSelectedNode[newSelectedNode.length - 2].children.findIndex((element) => {
                     return element.serialNr === newSelectedNode[newSelectedNode.length - 1].serialNr;
                  });
                  
                  console.log('Index within the children array of the parent before update:' + foundUp);
                      if(foundUp === 0){
                        newSelectedNode.pop();
                      }else{
                        newSelectedNode.pop(); 
                        if(false){//open?
                          newSelectedNode.push(newSelectedNode[newSelectedNode.length - 1].children[foundUp - 1].children[newSelectedNode[newSelectedNode.length - 1].children[foundUp - 1].children.length - 1]);
                        }else{
                          newSelectedNode.push(newSelectedNode[newSelectedNode.length - 1].children[foundUp - 1]);
                        } 
                      } 
              }
              break;
          case 40:
              console.log("Down");
              if(newSelectedNode.length > 1){
                  let foundDown = newSelectedNode[newSelectedNode.length - 2].children.findIndex((element) => {
                    return element.serialNr === newSelectedNode[newSelectedNode.length - 1].serialNr;
                  });
                  console.log(foundDown);
                  if(newSelectedNode[newSelectedNode.length - 2].children.length > 0
                  && foundDown < newSelectedNode[newSelectedNode.length - 2].children.length){
                      if(foundDown === newSelectedNode[newSelectedNode.length - 2].children.length){
                        newSelectedNode.pop();
                        //TODO next
                        
                      }else{
                        newSelectedNode.pop(); 
                        newSelectedNode.push(newSelectedNode[newSelectedNode.length - 1].children[foundDown + 1]);
                      } 
                  }

              }else{
                if(newSelectedNode[0].children.length > 0){
                  //TODO if(closed){nothing also auch kein push} if(open){nothing}
                  newSelectedNode.push(newSelectedNode[0].children[0])
                }
              } 

              // hier nochmal neu
              if(newSelectedNode.length > 1){
                  if(true){//open?
                      
                  }else{
                      
                  }
              }
              break;
          case 39:
              console.log("Right");
              if(newSelectedNode[newSelectedNode.length - 1].children.length !== 0){
                  //TODO if(open){nothing} if(closed){open} 
                  newSelectedNode.push(newSelectedNode[newSelectedNode.length - 1].children[0]);
              }
              break;
          case 37:
              console.log("Left");
              if(newSelectedNode.length !== 1){
                  //TODO if(open){close}
                  newSelectedNode.pop();
              }
              break;
        } 
        console.log(newSelectedNode[newSelectedNode.length - 1]);        
        this.selectNode(newSelectedNode);
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
  changed: boolean;
}
