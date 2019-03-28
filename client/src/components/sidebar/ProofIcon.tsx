import React from 'react';

import ProofNode, { Kind } from '../../key/prooftree/ProofNode';

import DisplayTreeNode from './displaytree/DisplayTreeNode';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import {
  faSquare as faSquareSolid,
  faVectorSquare,
  faSitemap,
  faPlusSquare,
  faDoorOpen,
  faCheckSquare,
} from '@fortawesome/free-solid-svg-icons';
import {
  faSquare,
  faCaretSquareDown,
  faMinusSquare,
} from '@fortawesome/free-regular-svg-icons';

/**
 * Displays a matching icon for a node within a proof tree, based on what kind
 * of node it is.
 */
export default class ProofIcon extends React.Component<Props, {}> {
  public render() {
    // if no specific icon can be determined, use a question mark as
    // default symbol
    let icon = faSquare;
    let color = '#cfd8dc';

    const red = '#FF5252';
    const green = '#4CAF50';
    const blue = '#00796B';

    // decide on a icon, based on the kind property
    switch (this.props.node.kind) {
      case Kind.OpenProofTree:
        icon = faVectorSquare;
        if (this.props.node.collapsed) {
          icon = faSquareSolid
        }
        color = red;
        break;

      case Kind.ClosedProofTree:
        icon = faVectorSquare;
        if (this.props.node.collapsed) {
          icon = faSquareSolid
        }
        color = green;
        break;

      case Kind.BranchNode:
        icon = faSitemap;
        break;

      case Kind.OpenGoal:
        icon = faDoorOpen;
        color = red;
        break;

      case Kind.ClosedGoal:
        icon = faCheckSquare;
        color = green;
        break;

      case Kind.OneStepSimplification:
        icon = faCaretSquareDown;
        break;

      default:
        break;
    }

    if (this.props.node.children.length > 0) {
      console.log('TEST');
      if (this.props.node.kind === Kind.DefaultNode) {
        if (this.props.node.collapsed) {
          icon = faPlusSquare;
        } else {
          icon = faMinusSquare;
        }
      }
    }

    return (
      <FontAwesomeIcon
        icon={icon}
        style={{ color: color, marginRight: '0.5em' }}
      />
    );
  }
}

interface Props {
  /** view model of the node, for which an icon shall be displayed. */
  node: DisplayTreeNode;
}
