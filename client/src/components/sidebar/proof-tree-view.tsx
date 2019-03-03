import React from 'react';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofResults from '../../key/netdata/ProofResults';

export default class ProofTreeView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
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
  nodes: ProofNode[];
  proofResults: ProofResults;
}

interface State {
}
