import React from 'react';

import PropTypes from 'prop-types';

import FileIcon from './file-icon.jsx';

/**
 * Displays a node and its children (recursively) in a filesystem-like tree.
 *
 * If the node has children, their visibility can be toggled by a single click
 * on it.
 *
 * It will be displayed using a file symbol (@see FileIcon) and the node name.
 * 
 * A file open action (double click on the node) can be handled, by providing
 * a `onOpenFile` handler. (`onOpenFile` : (filepath : [String]) -> ())
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
export default class FileNode extends React.Component {
    constructor(props) {
        super(props);

        this.state = {
            /** indicates, whether child nodes shall be visible or not*/
            'collapsed': false
        };
    }

    /** changes the visibility of this nodes children, if there are any. */
    toggle() {
        this.setState({
            'collapsed': !this.state.collapsed
        });
    }

    /**
      * Called, whenever the node is double clicked. Will fire the
      * `onOpenFile` handler with the node's path, if the node represents
      * a file.
      */
    handleItemDoubleClick() {
        if (this.props.data.type === 'file') {
            this.props.onOpenFile(this.props.path);
        }
    }

    render() {
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

        // Does the node have children?
        if (this.props.data.hasOwnProperty('contents')) {
            /*if so, are they visible / collapsed?
               (we'll use the css display property to hide them, if necessary)
            */
            const visibility = {
                'display': this.state.collapsed ?
                    'none'
                    : ''
            };

            return (
                <>
                    {/* allow toggling the visibility of the node's children
                        by a single click.

                        Double clicks are to be interpreted as opening files
                    */}
                    <div
                        onClick={() => {this.toggle();}}
                        onDoubleClick={this.handleItemDoubleClick.bind(this)}
                    >
                        {label}
                    </div>
                    {/* display the children as unordered list */}
                    <ul
                        className="projectTreeList"
                        style={visibility}
                    >
                        {
                            this.props.data.contents.map((child) =>
                                // when rendering components using map,
                                // react needs a unique key for each sub
                                // component
                                <li key={child.name}>
                                    {/* use recursion to display children.

                                        Add the child's name to the parent's
                                        path, to create it's own path.
                                    */}
                                    <FileNode
                                        data={child}
                                        path={this.props.path.concat([child.name])}
                                        onOpenFile={this.props.onOpenFile}
                                    />
                                </li>
                            )
                        }
                    </ul>
                </>
            );
        }

        else {
            return (
                /* double clicks are to be interpreted as opening files */
                <div
                    onDoubleClick={this.handleItemDoubleClick.bind(this)}
                >
                    {label}
                </div>
            );
        }
    }
}

FileNode.propTypes = {
    'onOpenFile': PropTypes.func,
    'data': PropTypes.shape({
        'name': PropTypes.string.isRequired,
        'type': PropTypes.oneOf(['file', 'folder']).isRequired,
        'contents': PropTypes.arrayOf(PropTypes.object)
    }).isRequired,
    'path': PropTypes.arrayOf(PropTypes.string)
};

FileNode.defaultProps = {
    'onOpenFile': () => {},
    'path': []
};
