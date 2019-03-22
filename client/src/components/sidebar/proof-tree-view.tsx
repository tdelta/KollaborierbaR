import React from 'react';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';

import ObligationResult, {
  ObligationResultKind,
} from '../../key/netdata/ObligationResult';

export default class ProofTreeView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.selectNode = this.selectNode.bind(this);
    this.state = {
      selectedNode: [],
    };
  }

  public selectNode(node: ProofNode[]) {
    this.setState({
      selectedNode: node,
    });
  }

  public render() {
    let node;
    const initiallyCollapsed = true;

    if (this.props.obligationResult != null) {
      node = this.props.obligationResult.proofTree;
      // Reenable, if this behavior is desired:
      //initiallyCollapsed = this.props.obligationResult.kind === ObligationResultKind.success;
    }

    if (node != null) {
      return (
        <div>
          <GuiProofNode
            key={`${node.serialNr},${node.oneStepId}`}
            // TODO better keys
            node={node}
            initiallyCollapsed={initiallyCollapsed}
            displaySequent={this.props.displaySequent}
            selectNode={this.selectNode}
            selectedNode={this.state.selectedNode}
            path={[node]}
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
  proofTreeOperationInfo: { operation: () => void; label: String };
}

interface State {
  selectedNode: ProofNode[];
}
