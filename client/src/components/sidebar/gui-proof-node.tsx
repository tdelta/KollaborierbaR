import React from 'react';

import PropTypes from 'prop-types';

import { Collapse, ListGroup, ListGroupItem } from 'reactstrap';
import './sidebar.css';

import ProofNode, { Kind } from '../../key/prooftree/ProofNode';

import { Context, ContextMenu, ContextAction } from './context.jsx';

import ProofIcon from './proof-icon';

export default class GuiProofNode extends React.Component<Props, State> {
  public static defaultProps = {
    initiallyCollapsed: false,
  };

  constructor(props: Props) {
    super(props);

    this.state = {
      /**
       * indicates, whether child nodes shall be visible or not
       */
      selected: false,
      collapsed:
        (this.props.node.kind !== Kind.ClosedProofTree &&
          this.props.node.kind !== Kind.OpenProofTree) ||
        this.props.initiallyCollapsed,
    };

    this.handleItemDoubleClick = this.handleItemDoubleClick.bind(this);
    this.toggle = this.toggle.bind(this);
  }

  public render() {
    // visible label of this node.
    // Consists of a file type specific icon and its name.
    const label = <>{this.props.node.text}</>;

    // Does the node have children? (checks for null *and* undefined)
    if (this.props.node.children != null) {
      /*if so, are they visible / collapsed?
               (we'll use the css display property to hide them, if necessary)
            */
      const display: object = {
        display: this.state.collapsed ? 'none' : '',
      };

      let background: string = 'inacticeFileNode';
      if (this.props.selectedNode.length === this.props.path.length) {
        background = 'activeFileNode';
        for (let i: number = 0; i < this.props.path.length; i++) {
          if (this.props.selectedNode[i].text !== this.props.path[i].text) {
            background = 'inactiveFileNode';
          }
        }
      }

      // Check whether the current node is the root node (need to display additional context menu)
      if (
        this.props.node.kind === 'OpenProofTree' ||
        this.props.node.kind === 'ClosedProofTree'
      ) {
        return (
          <>
            {/* allow toggling the visibility of the node's children
                          by a single click.
  
                          Double clicks are to be interpreted as opening files
                      */}
            <Context>
              <div
                onClick={this.toggle}
                onDoubleClick={this.handleItemDoubleClick}
                className={background}
              >
                <ProofIcon
                  node={this.props.node}
                  collapsed={this.state.collapsed}
                />
                {label}
              </div>
              <ContextMenu>
                <ContextAction
                  onClick={() =>
                    alert(
                      'Id:' +
                        this.props.node.serialNr +
                        'Kind' +
                        this.props.node.kind
                    )
                  }
                >
                  Show Id of proof node
                </ContextAction>
                <ContextAction
                  onClick={() =>
                    alert('TODO: Call save proof function provided by Anton')
                  }
                >
                  Save Proof
                </ContextAction>
                <ContextAction
                  onClick={() =>
                    alert(
                      'TODO: Call remove proof from history function provided by Anton'
                    )
                  }
                >
                  Remove Proof from History
                </ContextAction>
              </ContextMenu>
            </Context>

            {/* display the children as unordered list */}
            <ul className="projectTreeList" style={display}>
              {this.props.node.children.map(child => (
                // when rendering components using map,
                // react needs a unique key for each sub
                // component
                // TODO: Use better, unique key
                <li key={`${child.serialNr},${child.oneStepId}`}>
                  {/* use recursion to display children.
                   */}
                  <GuiProofNode
                    node={child}
                    displaySequent={this.props.displaySequent}
                    selectNode={this.props.selectNode}
                    selectedNode={this.props.selectedNode}
                    path={this.props.path.concat(child)}
                  />
                </li>
              ))}
            </ul>
          </>
        );
      } else {
        return (
          <>
            {/* allow toggling the visibility of the node's children
                        by a single click.

                        Double clicks are to be interpreted as opening files
                    */}
            <div
              onClick={this.toggle}
              onDoubleClick={this.handleItemDoubleClick}
              className={background}
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
                <li key={`${child.serialNr},${child.oneStepId}`}>
                  {/* use recursion to display children.
                   */}
                  <GuiProofNode
                    node={child}
                    displaySequent={this.props.displaySequent}
                    selectNode={this.props.selectNode}
                    selectedNode={this.props.selectedNode}
                    path={this.props.path.concat(child)}
                  />
                </li>
              ))}
            </ul>
          </>
        );
      }
    } else {
      // The node is a leaf
      return (
        /* double clicks are to be interpreted as opening files */
        <div onDoubleClick={this.handleItemDoubleClick}>{label}</div>
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
    const node = this.props.node;
    if (node.kind !== Kind.OneStepSimplification) {
      this.props.selectNode(this.props.path);
      this.props.displaySequent(node.sequent);
    }
  }
}

interface Props {
  node: ProofNode;
  initiallyCollapsed: boolean;
  displaySequent: (sequent: string) => void;
  selectNode: (path: ProofNode[]) => void;
  selectedNode: ProofNode[];
  path: ProofNode[];
}

interface State {
  collapsed: boolean;
  selected: boolean;
}
