import React from 'react';

import PropTypes from 'prop-types';

import { Collapse, ListGroup, ListGroupItem } from 'reactstrap';
import './sidebar.css';

import ProofNode, { Kind } from '../../key/prooftree/ProofNode';
import DisplayTreeNode from './displaytree/DisplayTreeNode';

import { Context, ContextMenu, ContextAction } from './context.jsx';

import ProofIcon from './ProofIcon';

/**
 * Visual representation of a step within a proof, a {@link ProofNode},
 * represented by a {@link DisplayTreeNode} within the rendered tree (view model).
 *
 * It displays a label for the node (based on {@link DisplayTreeNode#text}) and an
 * icon based on what kind of node it is (see {@link ProofIcon}).
 *
 * It is usually used as a part of an {@link ProofTreeView}.
 */
export default class GuiProofNode extends React.Component<Props> {
  constructor(props: Props) {
    super(props);

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
        display: this.props.node.collapsed ? 'none' : '',
      };

      //console.log('rerendering', this.props.node.collapsed);

      const background: string = this.props.node.selected
        ? 'activeFileNode'
        : 'inactiveFileNode';

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
                <ProofIcon node={this.props.node} />
                {label}
              </div>
              <ContextMenu>
                <ContextAction
                  onClick={this.props.proofTreeOperationInfo.operation}
                >
                  {this.props.proofTreeOperationInfo.label}
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
                    ref={child.getRef()}
                    selectNode={this.props.selectNode}
                    collapseNode={this.props.collapseNode}
                    proofTreeOperationInfo={this.props.proofTreeOperationInfo}
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
              <ProofIcon node={this.props.node} />
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
                    ref={child.getRef()}
                    selectNode={this.props.selectNode}
                    collapseNode={this.props.collapseNode}
                    proofTreeOperationInfo={this.props.proofTreeOperationInfo}
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
    this.props.collapseNode(this.props.node);
  }

  /**
   * Called, whenever the node is double clicked.
   */
  private handleItemDoubleClick() {
    const node = this.props.node;
    if (node.kind !== Kind.OneStepSimplification) {
      this.props.selectNode(this.props.node);
    }
  }
}

interface Props {
  /** view model of a node withing the proof tree */
  node: DisplayTreeNode;
  /** callback, which is invoked, if the node is selected by the user */
  selectNode: (node: DisplayTreeNode) => void;
  /** callback, which is invoked, when the node's children should be collapsed. */
  collapseNode: (node: DisplayTreeNode) => void;
  /**
   * Context menu item displayed only in the root node of the tree.
   * It contains a label that is displayed in
   * the menu and an operation that is executed when selecting the item.
   *
   * This is usually used to display a save / delete option for a proof
   */
  proofTreeOperationInfo: { operation: () => void; label: string };
}
