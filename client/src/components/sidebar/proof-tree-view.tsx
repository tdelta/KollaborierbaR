import React from 'react';
import { Kind } from '../../key/prooftree/ProofNode';

import ReactDOM from 'react-dom';

import GuiProofNode from './gui-proof-node';
import ProofNode from '../../key/prooftree/ProofNode';

import DisplayTreeNode, { toDisplayTree } from './displaytree/DisplayTreeNode';

import ObligationResult from '../../key/netdata/ObligationResult';

/**
 * Tree view for displaying proof trees (see {@link ProofNode}) in the UI.
 *
 * The resulting view provides the following features:
 *
 * 1. Collapsable nodes
 * 2. arrow key navigation
 * 3. Reactions to node selection (displaying corresponding sequent in editor)
 * 4. Context menu for saving and deleting proofs from history
 * ...
 */
export default class ProofTreeView extends React.Component<Props, State> {
  public selectedPath: DisplayTreeNode[] = [];
  public lastSelected: DisplayTreeNode | null = null;

  constructor(props: Props) {
    super(props);

    this.selectNode = this.selectNode.bind(this);
    this.handleKeydown = this.handleKeydown.bind(this);
    this.collapseNode = this.collapseNode.bind(this);
    this.state = {
      displayNode: null,
      changed: false,
    };
  }

  /*
   * Invert collapsed boolean of given DisplayTreeNode
   * @param given node
   */
  public collapseNode(node: DisplayTreeNode) {
    node.collapsed = !node.collapsed;
    this.setState({
      changed: true,
    });
  }

  /*
   * Marks the given DisplayTreeNode as selected
   * also scrolls selectNode into view
   * @param node given DisplayTreeNode
   */
  public selectNode(node: DisplayTreeNode) {
    this.props.displaySequent(node.sequent);
    console.log(node);

    if (node.getRef().current != null) {
      const component: GuiProofNode = node.getRef().current as GuiProofNode;
      const element = ReactDOM.findDOMNode(component) as Element;

      if (element != null) {
        element.scrollIntoView({});
      }
    }

    if (this.lastSelected) this.lastSelected.selected = false;
    if (node) node.selected = true;

    this.lastSelected = node;
    this.setState({
      changed: true,
    });
  }

  /*
   * Eventhandler for arrow buttons to navigate the proof tree
   * @param event keyevent
   */
  public handleKeydown(event: any) {
    if (this.lastSelected != null) {
      const leafNode: DisplayTreeNode = this.lastSelected;
      console.log(leafNode);
      switch (event.keyCode) {
        case 38:
          //Up
          event.preventDefault();
          if (leafNode.parent != null) {
            const parentNode: DisplayTreeNode = leafNode.parent;
            const index: number = parentNode.getIndex(leafNode);
            if (index > 0) {
              this.selectNode(parentNode.children[index - 1].findNextLeafUp());
            } else {
              this.selectNode(parentNode);
            }
          }
          break;
        case 40:
          // Down
          event.preventDefault();
          if (
            !leafNode.collapsed &&
            leafNode.children.length !== 0 &&
            leafNode.children[0].kind !== Kind.OneStepSimplification
          ) {
            this.selectNode(leafNode.children[0]);
          } else {
            if (leafNode.parent != null) {
              const nextLeafDown: DisplayTreeNode | null = leafNode.findNextLeafDown();
              if (nextLeafDown != null) {
                this.selectNode(nextLeafDown);
              }
            } else {
              this.selectNode(leafNode);
            }
          }
          break;
        case 39:
          // Right
          event.preventDefault();
          leafNode.collapsed = false;
          this.selectNode(leafNode);
          break;
        case 37:
          // Left
          event.preventDefault();
          leafNode.collapsed = true;
          this.selectNode(leafNode);
          break;
      }
    }
  }

  /**
   * Registers key handlers (for arrow controls) and builds view model, as soon
   * as the view is being rendered the first time.
   */
  public componentDidMount() {
    document.addEventListener('keydown', this.handleKeydown);

    this.convertToDisplayTree();
  }

  /**
   * Unregisters the handlers, which have been installed in {@link #componentDidMount}
   */
  public componentWillUnmount() {
    document.removeEventListener('keydown', this.handleKeydown);
  }

  /**
   * Rebuilds the view model, if the displayed proof changed.
   */
  public componentDidUpdate(prevProps: Props) {
    if (prevProps.obligationResult !== this.props.obligationResult) {
      this.convertToDisplayTree();
    }
  }

  /**
   * Helper method for building the view model from the proof tree which is being
   * displayed by this view.
   *
   * It also updates the this components React state with the new model and
   * sets a flag to indicate it changed.
   */
  private convertToDisplayTree() {
    let displayNode: DisplayTreeNode | null = null;
    if (this.props.obligationResult != null) {
      displayNode = toDisplayTree(this.props.obligationResult.proofTree, null);
    }

    this.setState({
      changed: true,
      displayNode: displayNode,
    });
  }

  /**
   * React lifecycle rendering method.
   * {@see https://reactjs.org/docs/react-component.html#render}
   *
   * See class documentation for information on what is being rendered.
   */
  public render() {
    let node;
    let displayNode;

    // if there is a proof to be displayed, fetch the root node and the
    // view model
    if (this.props.obligationResult != null) {
      node = this.props.obligationResult.proofTree;
      displayNode = this.state.displayNode;
      // Reenable, if this behavior is desired:
      //initiallyCollapsed = this.props.obligationResult.kind === ObligationResultKind.success;
    }

    if (node != null && displayNode != null) {
      return (
        <div>
          <GuiProofNode
            key={`${node.serialNr},${node.oneStepId}`}
            ref={displayNode.getRef()}
            node={displayNode}
            selectNode={this.selectNode}
            collapseNode={this.collapseNode}
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
  /** proof being displayed */
  obligationResult?: ObligationResult;
  /** callback being invoked, if a node in the displayed tree is clicked on, to display its sequent in the editor */
  displaySequent: (sequent: string) => void;
  /**
   * Context menu item displayed in the root node, a label that is displayed in
   * the menu and an operation that is executed when selecting the item.
   *
   * This is usually used to display a save / delete option for a proof
   */
  proofTreeOperationInfo: { operation: () => void; label: string };
}

interface State {
  displayNode: DisplayTreeNode | null;
  changed: boolean;
}
