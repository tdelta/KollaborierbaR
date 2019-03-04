import React from 'react';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofResults from '../../key/netdata/ProofResults';

export default class ProofTreeView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.selectNode = this.selectNode.bind(this);
    this.state = {
      selectedNode: []
    };
  }

  public selectNode(node: ProofNode[]){
    this.setState({
      selectedNode: node
    });
  }

  public render() {
    let nodes: ProofNode[] = [];
    
    const results = this.props.proofResults;
    if (results != null) {
      nodes =
        results.succeeded
          .concat(results.failed)
          .concat(results.errors)
          .map(result => result.proofTree)
          .filter(proofTree => proofTree != null);
    }
      
    // TODO better keys

    if (nodes.length > 0) {
      return (
        <div>
          {
            nodes.map(node => (
                <GuiProofNode
                  key={node.text}
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
