import React from 'react';

import PropTypes from 'prop-types';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import FileNode from './file-node.jsx';

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
                {projectTitle}

                <hr />
            </>
        );

        // if the project is not empty, display its contents
        if (this.props.project.hasOwnProperty('contents')) {
            return (
                <>
                    {header}

                    {
                        this.props.project.contents.map((item) =>
                            <FileNode
                                key={item.name}
                                data={item}
                                path={[item.name]}
                                onOpenFile={this.props.onOpenFile}
                            />
                        )
                    }
                </>
            );
        }

        else {
            return (<>{header}</>);
        }
    }
}

ProjectTreeView.propTypes = {
    'onOpenFile': PropTypes.func,
    'project': PropTypes.shape({
        'contents': PropTypes.arrayOf(PropTypes.object),
        'name': PropTypes.string.isRequired
    }).isRequired
};

ProjectTreeView.defaultProps = {
    'onOpenFile': () => {}
};
        
