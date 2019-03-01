import React from 'react';

import PropTypes from 'prop-types';

import { Collapse, ListGroup, ListGroupItem } from 'reactstrap';
import './sidebar.css';

import Node, {Kind} from '../../key/webui/prooftree/Node';

import ProofIcon from './proof-icon';

export default class ProofNode extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);

    this.state = {
      /**
       * indicates, whether child nodes shall be visible or not
       */
      selected: false,
      collapsed: this.props.node.kind !== Kind.ClosedProofTree &&
                 this.props.node.kind !== Kind.OpenProofTree
    };

    this.handleItemDoubleClick = this.handleItemDoubleClick.bind(this);
    this.toggle = this.toggle.bind(this);
  }

  public render() {
    // visible label of this node.
    // Consists of a file type specific icon and its name.
    const label = (
      <>
        {this.props.node.text}
      </>
    );

    // Does the node have children? (checks for null *and* undefined)
    if (this.props.node.children != null) {
      /*if so, are they visible / collapsed?
               (we'll use the css display property to hide them, if necessary)
            */
      const display: object = {
        display: this.state.collapsed ? 'none' : '',
      };

      return (
        <>
          {/* allow toggling the visibility of the node's children
                        by a single click.

                        Double clicks are to be interpreted as opening files
                    */}
          <div
            onClick={this.toggle}
            onDoubleClick={this.handleItemDoubleClick}
          >
            <ProofIcon
              node={this.props.node}
              collapsed={this.state.collapsed}
            />
            {label}
          </div>
          {/* display the children as unordered list */}
          <ul className="projectTreeList" style={display}>
            {this.props.node.children.map(child => (
              // when rendering components using map,
              // react needs a unique key for each sub
              // component
              // TODO: Use better, unique key
              <li key={child.text}>
                {/* use recursion to display children.
                */}
                <ProofNode
                  node={child}
                />
              </li>
            ))}
          </ul>
        </>
      );
    } else {
      // The node is a leaf
      return (
        /* double clicks are to be interpreted as opening files */
        <div
          onDoubleClick={this.handleItemDoubleClick}
        >
          {label}
        </div>
      );
    }
  }

  /** changes the visibility of this nodes children, if there are any. */
  private toggle() {
    this.setState({
      collapsed: !this.state.collapsed,
    });
  }

  /**
   * Called, whenever the node is double clicked. */
  private handleItemDoubleClick() {
    // TODO
  }
}

interface Props {
  node: Node;
}

interface State {
  collapsed: boolean;
  selected: boolean;
}
