import React from 'react';

import PropTypes from 'prop-types';

import FileIcon from './file-icon.jsx';
import { Collapse, ListGroup, ListGroupItem } from 'reactstrap';
import './sidebar.css'
/**
 * Displays a node and its children (recursively) in a filesystem-like tree.
 *
 * If the node has children, their visibility can be toggled by a single click
 * on it.
 *
 * It will be displayed using a file symbol (@see FileIcon) and the node name.
 *
 * A file open action (double click on the node) can be handled, by providing
 * a `onOpenFile` handler. (`onOpenFile` : (filepath: string[]) => void)
 *
 * Example:
 *
 * (comments need to be removed for this to work (since its jsx))
 *
 * ```jsx
 *     <FileNode
 *         data={{ //filesystem-like structure
 *             'name': 'java', // displayed name of this node
 *             'type': 'folder', // type can be 'file' or 'folder'
 *             'contents': [ // children will be rendered, if contents are given
 *                 { // recursive data strucure
 *                     'name': 'child.java',
 *                     'type': 'file'
 *                 }
 *              ]
 *          }}
 *          path={['src', 'main']} // path within filesystem/project, at
 *                                 // which this node lives.
 *                                 // It will be used to supply the onOpenFile
 *                                 // handler with a path to the double clicked
 *                                 // file.
 *          onOpenFile={(path) => {
 *              console.log(path);
 *              //will yield ['src', 'java', 'main', 'child.java'],
 *              //if the child.java node is double clicked
 *          }}
 *     />
 * ```
 */
export default class FileNode extends React.Component<Props, State> {
  public static propType = {
    onOpenFile: PropTypes.func,
    data: PropTypes.shape({
      name: PropTypes.string.isRequired,
      type: PropTypes.oneOf(['file', 'folder']).isRequired,
      contents: PropTypes.arrayOf(PropTypes.object),
    }).isRequired,
    path: PropTypes.arrayOf(PropTypes.string),
  };

    private node: HTMLDivElement | null;
  public static defaultProps = {
    onOpenFile: () => undefined,
    path: [],
  };


  constructor(props: Props) {
    super(props);
    this.node = null;

    this.state = {
      /**
       * indicates, whether child nodes shall be visible or not
       */
      selected: false,
      collapsed: false,
      context: false,
    };

    this.handleItemDoubleClick = this.handleItemDoubleClick.bind(this);
      this.handleRightClick = this.handleRightClick.bind(this);
      this.handleContextClose = this.handleContextClose.bind(this);
    this.toggle = this.toggle.bind(this);
  }

  public render() {
    // visible label of this node.
    // Consists of a file type specific icon and its name.
    const label = (
      <>
        <FileIcon
          className="projectTreeIcon"
          data={this.props.data}
          isOpen={!this.state.collapsed}
        />
        {this.props.data.name}
      </>
    );

    // Does the node have children? (checks for null *and* undefined)
    if (this.props.data.contents != null) {
      /*if so, are they visible / collapsed?
               (we'll use the css display property to hide them, if necessary)
            */
      const display: object = {
        display: this.state.collapsed ? 'none' : '',
      };

      const background: object = {
        backgroundColor: this.state.selected ? '#f00' : '#0f0',
      };

      return (
        <>
          {/* allow toggling the visibility of the node's children
                        by a single click.

                        Double clicks are to be interpreted as opening files
                    */}
          <div onClick={this.toggle} onDoubleClick={this.handleItemDoubleClick} >
            {label}
          </div>
          {/* display the children as unordered list */}
          <ul className="projectTreeList" style={display}>
            {this.props.data.contents.map(child => (
              // when rendering components using map,
              // react needs a unique key for each sub
              // component
              <li key={child.name}>
                {/* use recursion to display children.

                                        Add the child's name to the parent's
                                        path, to create it's own path.
                                    */}
                <FileNode
                  tree={this.props.tree}
                  data={child}
                  path={this.props.path.concat([child.name])}
                  onOpenFile={this.props.onOpenFile}
                  onOpenContext={this.props.onOpenContext}
                  onSelect={this.props.onSelect}
                  selectedPath={this.props.selectedPath}
                />
              </li>
            ))}
          </ul>
        </>
      );
    } else {
      // The node is a single file
      const background =
        this.props.selectedPath === this.props.path.join('/')
          ? 'activeFileNode'
          : 'inactiveFileNode';
      return (
        /* double clicks are to be interpreted as opening files */
        <div ref={elem => this.node = elem} onDoubleClick={this.handleItemDoubleClick} onContextMenu={this.handleRightClick} className={background}>
          {label}
       <Collapse isOpen={this.state.context}>
         <ListGroup compact className='contextList'>
            <li className='contextItem'>Delete File</li>
            <li className='contextItem'>Rename File</li>
          </ListGroup>
        </Collapse>
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
   * Called, whenever the node is double clicked. Will fire the
   * `onOpenFile` handler with the node's path, if the node represents
   * a file.
   */
  private handleItemDoubleClick() {
    if (this.props.data.type === 'file') {
      this.props.onOpenFile(this.props.path);
      this.props.onSelect(this.props.path.join('/'));
    }
  }

  private handleContextClose(e: Event) {
    e.preventDefault();
    if (e.target !== this.node) {
      this.setState({ context: false });
    }
  }
  private handleRightClick() {
    this.props.onOpenContext(this.props.path);
      this.setState({ context: !this.state.context });
    
  }

  componentDidUpdate() {
    // When the component is mounted, add your DOM listener to the "nv" elem.
    // (The "nv" elem is assigned in the render function.)
      if (this.props.tree() != null){

        console.log("Sucess")
        this.props.tree().addEventListener("contextmenu", this.handleContextClose);
      }
      else {
        console.log("Fail")
      }
  }

  componentWillUnmount() {
    // Make sure to remove the DOM listener when the component is unmounted.
        this.props.tree().removeEventListener("contextmenu", this.handleContextClose);
  }
}

enum FileType {
  file = 'file',
  folder = 'folder',
}

interface FileNodeData {
  name: string;
  type: FileType;
  contents?: [FileNodeData];
}

interface Props {
  onOpenFile: (path: string[]) => void;
  onOpenContext: (path: string[]) => void;
  onSelect: (path: string) => void;
  data: FileNodeData;
  tree: () => HTMLDivElement;
  selectedPath: string;
  path: string[];
}

interface State {
  collapsed: boolean;
  selected: boolean;
  context: boolean;
}
