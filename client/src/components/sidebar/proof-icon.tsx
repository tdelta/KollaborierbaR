import React from 'react';

import ProofNode, {Kind} from '../../key/prooftree/ProofNode';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import { faSquare as faSquareSolid, faVectorSquare, faSitemap, faPlusSquare, faDoorOpen, faCheckSquare } from '@fortawesome/free-solid-svg-icons';
import { faSquare, faCaretSquareDown, faMinusSquare } from '@fortawesome/free-regular-svg-icons';

export default class ProofIcon extends React.Component<Props, {}> {
    render() {
        // if no specific icon can be determined, use a question mark as
        // default symbol
        let icon = faSquare;
        let color = '#cfd8dc';

        const red = '#FF5252';
        const green = '#4CAF50';
        const blue = '#00796B';

        // check, whether the file in question is actually a file or a folder
        switch (this.props.node.kind) {
            case Kind.OpenProofTree:
                icon = faVectorSquare;
                color = red;
                break;

            case Kind.ClosedProofTree:
                icon = faVectorSquare;
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
          if (this.props.node.kind === Kind.DefaultNode) {
            if (this.props.collapsed) {
              icon = faPlusSquare;
            }

            else {
              icon = faMinusSquare;
            }
          }

          else if (
            this.props.node.kind === Kind.OpenProofTree ||
            this.props.node.kind == Kind.ClosedProofTree
          ) {
            if (this.props.collapsed) {
              icon = faSquareSolid;
            }
          }
        }

        return (
          <FontAwesomeIcon
              icon={icon}
              style={{color: color, marginRight: '0.5em'}}
            />
        );
    }
}

interface Props {
  node: ProofNode;
  collapsed: boolean;
}
