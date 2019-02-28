import React from 'react';

import ProofNode from './proof-node';
import Node from '../../key/webui/prooftree/Node';

export default class ProofTreeView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
  }

  public render() {
    const areNodesValid = this.props.nodes && this.props.nodes.length > 0;

    // TODO better keys

    if (areNodesValid) {
      return (
        <div>
          {
          this.props.nodes.map(node => (
            <ProofNode
              key={node.text}
              // TODO better keys
              node={node}
            />
          ))}
        </div>
      );
    } else {
      return <>No open proof.</>;
    }
  }
}

// defining the structure of this react components properties
interface Props {
  nodes: Node[];
}

interface State {
}
