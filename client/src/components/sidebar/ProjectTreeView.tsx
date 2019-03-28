import React from 'react';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import {
  faBomb,
  faFolderPlus,
  faFileMedical,
} from '@fortawesome/free-solid-svg-icons';

import FileNode from './FileNode';
import { Context, ContextMenu, ContextAction } from './context.jsx';

import Project from '../../Project';
import FileOrFolder, { sort as fileSort } from '../../FileOrFolder';

/**
 * Displays a project (file system like JSON structure, passed by `project`
 * property, @see {@link Project}).
 *
 * It will show the project's name (@link project.name) and render the project tree
 * using the {@link FileNode} component.
 *
 * Actions on the project tree (creating files etc.) will trigger handlers, which
 * can be passed using the properties (@see {@link Props}).
 */
export default class ProjectTreeView extends React.Component<Props, {}> {
  // default values for some properties
  public static defaultProps = {
    onOpenFile: () => undefined,
    onDeleteFile: () => undefined,
    onCreateFile: () => undefined,
  };

  /**
   * React lifecycle rendering method.
   * {@link https://reactjs.org/docs/react-component.html#render}
   *
   * See constructor documentation for information on what is being rendered.
   */
  public render() {
    // determine, whether the project property is set and
    // contains at least a name. If not, the view will show an appropriate message.
    const isProjectValid = this.props.project && this.props.project.name;
    // ^ the project object must at least contain a name

    let projectTitle;
    if (isProjectValid) {
      projectTitle = ( // if there is a valid project, render its name
        <>
          <FontAwesome name="cube" className="projectTreeIcon" />{' '}
          {this.props.project.name}
        </>
      );
    } else {
      projectTitle = ( // if not, render a message
        <>
          <FontAwesome name="expand" className="projectTreeIcon" /> No open
          project
        </>
      );
    }

    // Always display the project's name (...and a little icon on the left).
    // Also add a context menu to the displayed project name, so that the project
    // tree may be manipulated using it.
    const header = (
      <>
        <div className="tableFileNode">
          <Context>
            {projectTitle}
            <ContextMenu>
              {isProjectValid?
                <>
                  <ContextAction
                    icon={faFolderPlus}
                    onClick={() => this.props.onCreateFile([], 'folder')}
                  >
                    Create Folder
                  </ContextAction>
                  <ContextAction
                    icon={faFileMedical}
                    onClick={() => this.props.onCreateFile([], 'file')}
                  >
                    Create File
                  </ContextAction>
                  {/*<ContextAction>Rename Project</ContextAction>*/}
                  <ContextAction
                    icon={faBomb}
                    onClick={() =>
                      this.props.onDeleteProject(this.props.project.name)
                    }
                  >
                    Delete Project
                  </ContextAction>
                </>
                : <></>
              }
            </ContextMenu>
          </Context>
        </div>
        <hr />
      </>
    );

    // if the project is not empty, display its contents
    if (isProjectValid && this.props.project.hasOwnProperty('contents')) {
      const sorted: FileOrFolder[] = fileSort(this.props.project.contents);

      return (
        <>
          <div>
            {header /* display the header (contains project name) */}
            {// render each element within the root folder of the
            // project as FileNode
            sorted.map(item => (
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
                onUpdateFileName={this.props.onUpdateFileName}
                openedPath={this.props.openedPath}
              />
            ))}
          </div>
        </>
      );
    } else {
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

interface Props {
  /** Currently open project structure, which will be rendered as tree */
  project: Project;
  /** Called, when a file is double clicked */
  onOpenFile: (path: string[]) => void;
  /** Called, when the delete context option is selected on an item in the project tree view */
  onDeleteFile: (path: string[]) => void;
  /**
   * Called, when the user selects the file creation option in the project tree view.
   *
   * @param path   file path to where the file shall be created. The items in the array
   *               are folders except for the last item, which shall be the name of the
   *               new file
   * @param type   decides, whether a file or a folder is being created.
   *               Possible values: 'file' or 'folder'
   */
  onCreateFile: (path: string[], type: string) => void;
  /** Called, when the project deletion context option is selected in the project tree view */
  onDeleteProject: (path: string) => void;
  /** Called, when a file is being renamed by the user using the project tree view */
  onUpdateFileName: (path: string[]) => void;
  /** Path of currently opened file. Used to highlight it in the tree */
  openedPath: string[];
}
