import React from 'react';

import PropTypes from 'prop-types';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import FileNode from './file-node.tsx';
import {Context, ContextMenu, ContextAction} from './context.jsx';

/**
 * Displays a project (file system like JSON structure, passed by `project`
 * property).
 *
 * It will show the project's name (`project.name`) and render the project tree
 * using the FileNode component. For further details see the FileNode component.
 *
 * If the user opens a file within the displayed tree (double click), it can be
 * handled by passing a `onOpenFile` handler property. (Also see FileNode),
 *
 * For details about required property parameters, see propTypes section
 * at the end of this file.
 *
 * Example:
 *
 * ```jsx
 *     <ProjectTreeView
 *         project={{
 *             'name': 'My Project',
 *             'contents': [
 *                 {
 *                     'name': 'src',
 *                     'type': 'folder',
 *                     'contents': [
 *                         {'name': 'Test.java', 'type': 'file'}
 *                     ]
 *                 },
 *                 {'name': 'README.md', 'type': 'file'}
 *              ]
 *         }}
 *         onOpenFile={(path) => console.log(path)}
 *     />
 * ```
 */
export default class ProjectTreeView extends React.Component {

    render() {
        // determine, whether the project property is set and
        // contains at least a name. If not, the view will show an appropriate message.
        const isProjectValid =
               this.props.project // the project property is set to something
            && this.props.project.name;
            // ^ the project object must at least contain a name

        var projectTitle;
        if (isProjectValid) {
            projectTitle = ( // if there is a valid project, render its name
                <>
                    <FontAwesome
                        name='cube'
                        className="projectTreeIcon"
                    /> {this.props.project.name}
                </>
            );
        } else {
            projectTitle = ( // if not, render a message
                <>
                    <FontAwesome
                        name='expand'
                        className="projectTreeIcon"
                    /> No open project
                </>
            );
        }

        // Always display the project's name.
        // (...and a little icon on the left)
        const header = (
            <>
                        <Context tree={() => this.state.file}>
                            {projectTitle}
                            <ContextMenu>
                                <ContextAction onClick={() => this.props.onDeleteProject(this.props.project.name)}>Delete Project</ContextAction>
                                {/*<ContextAction>Rename Project</ContextAction>*/}
                                <ContextAction onClick={() => this.props.onCreateFile([], 'folder')}>Create Folder</ContextAction>
                                <ContextAction onClick={() => this.props.onCreateFile([], 'file')}>Create File</ContextAction>
                            </ContextMenu>
                        </Context>
                <hr />
            </>
        );

        // if the project is not empty, display its contents
        if (isProjectValid && this.props.project.hasOwnProperty('contents')) {
            return (
                <>
                    <div>
                        {header /* display the header (contains project name) */}

                        {
                            // render each element within the root folder of the
                            // project as FileNode
                            this.props.project.contents.map((item) =>
                                <FileNode
                                    key={item.name}
                                    // ^when rendering a list of elements, react
                                    // requires a unique key for all of them
                                    data={item} // pass the element to thee FileNode
                                    path={[item.name]}
                                    // ^since this is the root of the project,
                                    // the path of each element consists just of its
                                    // own name
                                    onOpenFile={this.props.onOpenFile}
                                    onDeleteFile={this.props.onDeleteFile}
                                    onCreateFile={this.props.onCreateFile}
                                    onUpdateFile={this.props.onUpdateFile}
                                    onOpenContext={this.props.onOpenContext}
                                    openedPath={this.props.openedPath}
                                />
                            )
                        }
                    </div>
                </>
            );
        }

        else {
            // if there are no contents, just render the title and a message
            // about missing contents
            return (
                <>
                  {header}

                  There are no files.
                </>
            );
        }
    }
}

// declare types of properties
ProjectTreeView.propTypes = {
    'onOpenFile': PropTypes.func,
    'onOpenContext': PropTypes.func,
    'onDeleteFile': PropTypes.func,
    'onDeleteProject': PropTypes.func,
    'onCreateFile': PropTypes.func,
    'openedPath': PropTypes.arrayOf(PropTypes.string),
    'project': PropTypes.shape({
        'contents': PropTypes.arrayOf(PropTypes.object),
        'name': PropTypes.string
    })
};

// default values for some properties
ProjectTreeView.defaultProps = {
    'onOpenFile': () => {},
    'onDeleteFile': () => {},
    'onCreateFile': () => {},
};
        
