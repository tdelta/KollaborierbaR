import NotificationSystem from 'react-notification-system';

import { UserIndicatorData } from './components/user-names/user-indicator-data';
import UserIndicator from './components/user-names/user-indicator';
import { serverAddress } from './constants';
import ConfirmationModal from './components/confirmation-modal';
import Usernames from './components/user-names/user-names';

import { Network } from './network';

import ProjectController, {
  ProjectEvent,
  RenamedFileEvent,
  ProjectFileEvent,
  UsersUpdatedEvent,
  ProjectEventType,
} from './collaborative/ProjectController';

import FileOrFolder, { FileFolderEnum } from './FileOrFolder';
import Project from './Project';

interface OpenFileData {
  fileName: string;
  fileText: string;
}

// define the structure received KeY results
interface ProofResults {
  succeeded: string[];
  failed: string[];
  errors: string[];
}

export default class ProjectManagement {
  private showProject: (p: Project | {}) => void;
  private getCurrentProject: () => Project | {};
  private setText: (s: string) => void;
  private setFileName: (name: string | undefined) => void;
  private getOpenedPath: () => string[];
  private setOpenedPath: (path: string[]) => void;
  private confirmationModal: React.RefObject<ConfirmationModal>;
  private notificationSystem: React.RefObject<NotificationSystem.System>;
  private openFile: (path: string[]) => void;
  private projectController: ProjectController;

  constructor(
    network: Network,
    showProject: (p: Project | {}) => void,
    getCurrentProject: () => Project | {},
    setText: (s: string) => void,
    setFileName: (name: string | undefined) => void,
    getOpenedPath: () => string[],
    setOpenedPath: (path: string[]) => void,
    confirmationModal: React.RefObject<ConfirmationModal>,
    notificationSystem: React.RefObject<NotificationSystem.System>,
    openFile: (path: string[]) => void
  ) {
    this.showProject = showProject;
    this.getCurrentProject = getCurrentProject;
    this.setText = setText;
    this.setFileName = setFileName;
    this.getOpenedPath = getOpenedPath;
    this.setOpenedPath = setOpenedPath;
    this.confirmationModal = confirmationModal;
    this.notificationSystem = notificationSystem;
    this.openFile = openFile;

    this.projectController = new ProjectController(network, {
      onProjectEvent: (
        event:
          | ProjectEvent
          | RenamedFileEvent
          | ProjectFileEvent
          | UsersUpdatedEvent
      ) => {
        const currentProject = this.getCurrentProject();
        console.log(event.eventType);
        switch (event.eventType) {
          case ProjectEventType.DeletedFile:
            this.openProject((currentProject as Project).name, false);

            if (
              !ProjectManagement.projectContainsPath(
                currentProject as Project,
                this.getOpenedPath()
              )
            ) {
              this.setText('');
              this.setOpenedPath([]);
            }

            if (this.notificationSystem.current) {
              this.notificationSystem.current.clearNotifications();
              this.notificationSystem.current.addNotification({
                message: 'A file got deleted',
                level: 'error',
                position: 'bc',
              });
            }

            break;
          case ProjectEventType.RenamedFile:
            this.openProject((currentProject as Project).name, false);

            const renameEvent: RenamedFileEvent = event as RenamedFileEvent;

            if (renameEvent.originalPath === this.getOpenedPath().join('/')) {
              // TODO: Evtl abstimmen mit Collab controller
              const newPathArray: string[] = renameEvent.newPath.split('/');

              if (newPathArray.length < 1) {
                console.log('Error: Updated file path is invalied.');
              } else {
                this.setFileName(newPathArray[newPathArray.length - 1]);
                this.setOpenedPath(newPathArray);
              }
            }

            if (this.notificationSystem.current) {
              this.notificationSystem.current.clearNotifications();
              this.notificationSystem.current.addNotification({
                message: `File ${renameEvent.originalPath} got renamed to ${
                  renameEvent.newPath
                }.`,
                level: 'info',
                position: 'bc',
              });
            }

            break;
          case ProjectEventType.UpdatedFile:
            const fileEvent: ProjectFileEvent = event as ProjectFileEvent;

            if (fileEvent.filePath === this.getOpenedPath().join('/')) {
              if (this.notificationSystem.current) {
                this.notificationSystem.current.clearNotifications();
                this.notificationSystem.current.addNotification({
                  message: `Permanently saved the contents of your currently opened file.`,
                  level: 'success',
                  position: 'bc',
                });
              }
            }

            break;
          case ProjectEventType.DeletedProject:
            this.showProject({});
            this.setText('');
            this.setOpenedPath([]);

            if (this.notificationSystem.current) {
              this.notificationSystem.current.clearNotifications();
              this.notificationSystem.current.addNotification({
                message: 'Your project got deleted.',
                level: 'error',
                position: 'bc',
              });
            }

            break;
          case ProjectEventType.UpdatedProject:
            if (
              !(
                (currentProject as any).name == null ||
                (currentProject as any).contents == null
              )
            ) {
              this.openProject((currentProject as Project).name, false);

              if (
                !ProjectManagement.projectContainsPath(
                  currentProject as Project,
                  this.getOpenedPath()
                )
              ) {
                this.setText('');
                this.setOpenedPath([]);
              }
            }

            if (this.notificationSystem.current) {
              // TODO evtl. nicht alle Notifications entfernen
              this.notificationSystem.current.clearNotifications();
              this.notificationSystem.current.addNotification({
                message: 'The project files got updated.',
                level: 'info',
                position: 'bc',
              });
            }

            break;
          case ProjectEventType.UsersUpdated:
            console.log(event);
            Usernames.updateUsers((event as UsersUpdatedEvent).users);
            break;
        }
      },
    });
  }

  /**
   * Recursively searches the current project files for all files that end with ".script"
   * And returns their absolute paths.
   *
   * @return - An array of filepaths
   */
  public getMacroFiles(): string[] {
    const project: Project | {} = this.getCurrentProject();
    if ('contents' in project) {
      return (project as Project).contents
        .map(item => this.getMacroFilesRec('', item))
        .reduce((x: string[], y: string[]) => x.concat(y), []); // flatMap does not exist in IE
    } else {
      return [];
    }
  }

  /**
   * Recursive helper function. Given the path to the file or folder item, returns
   * an array of absolute paths to all .script files contained in item
   *
   * @param parentName - path to item, e.g. /src if item is the file Main.java in /src/Main.java
   * @param item - the file or folder to search in
   * @return - an array of filepaths
   */
  private getMacroFilesRec(parentName: string, item: FileOrFolder): string[] {
    if (item.type === FileFolderEnum.file && item.name.endsWith('.script')) {
      // item is a macro file
      return [`${parentName}/${item.name}`];
    } else if (item.contents) {
      // item is a directory
      return item.contents
        .map(child =>
          this.getMacroFilesRec(`${parentName}/${item.name}`, child)
        )
        .reduce((x: string[], y: string[]) => x.concat(y), []); // flatMap does not exist in IE
    } else {
      return [];
    }
  }

  private static projectContainsPath(
    project: Project,
    path: string[]
  ): boolean {
    const contentRecursion = (
      file: FileOrFolder,
      subPath: string[]
    ): boolean => {
      if (subPath.length < 1) {
        return false;
      } else if (subPath.length === 1) {
        return file.name === subPath[0];
      } else if (file.contents == null) {
        return false;
      } else {
        return file.contents.some(subFile =>
          contentRecursion(subFile, subPath.slice(1))
        );
      }
    };

    return project.contents.some(file => contentRecursion(file, path));
  }

  /**
   * Fetches contents and metadata of a file asynchronously from the server via
   * HTTP request.
   *
   * @param {string} path: path to file that shall be opened.
   *     It shall contain a leading '/' and the first folder shall be the
   *     project name.
   *
   * @returns {Promise} promise which will resolve to said contents and metadata.
   *
   * @example
   * openFile('/My Project/README.md').then((response) =>
   *   console.log(response.fileName); // yields "README.md"
   *   console.log(response.fileText); // yields contents of the README.md file
   * });
   */
  public static openFile(path: string): Promise<OpenFileData> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    const url = `${serverAddress}/projects/${escapedPath}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => {
      if (response.status === 200) {
        console.log('Parsing open file response: ', response);

        return response.json();
      } else {
        console.error('Opening file failed.', response);
      }
    }); // parse the response body as json
  }

  /*
   * load the list of available projects from the server
   */
  public static getProjects(): Promise<string[]> {
    const url = `${serverAddress}/projects`;
    return fetch(url, {
      method: 'GET',
      mode: 'cors',
      headers: {
        Accept: 'application/json',
      },
    }).then(response => response.json());
  }

  /*
   * load the related files for the project with name 'name' from the server
   * the handler displays the returned project in the editor
   */
  public openProject(name: string, resetFile: boolean = true): void {
    const escapedName = escape(name);

    const url = `${serverAddress}/projects/${escapedName}`;

    this.closeProject(() =>
      this.projectController
        .openProject(name)
        .catch(e => {
          console.error('Could not sync with server to open project');
          console.error(e);
        })
        .then(() =>
          fetch(url, {
            method: 'GET',
            mode: 'cors',
          }).then(response => {
            response.json().then((json: Project) => {
              this.showProject(json);

              if (resetFile) {
                this.setText('');
                this.setOpenedPath([]);
              }
            });
            //return {'status': response.status,
            //  'statusText': response.statusText};
          })
        )
    );
  }

  public closeProject(cb: () => void): void {
    const project = this.getCurrentProject();

    if ((project as Project).name == null) {
      cb();
    } else {
      this.projectController
        .closeProject((project as Project).name)
        .catch(e => {
          console.error(
            'Failed to unsubscribe, you may still receive messages for your closed project'
          );
          console.error(e);
          cb();
        })
        .then(cb);
    }
  }

  /*
   * Calls the REST delete method. only used internally
   * TODO: Better explanation, what this method does
   */
  private static deleteOverall(path: string): Promise<Project | {}> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/projects/${escapedPath}`;

    return fetch(url, {
      method: 'DELETE',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
      },
    })
      .then(response => response.json()) // parse the response body as json
      .catch(() => undefined); // if the json body is empty (e.g. after project delete) return an empty json object
  }

  /*
   * Deletes a file from the loaded project on the server
   */
  public deleteFile(
    currentlyOpenFile: string[],
    projectName: string,
    path: string[]
  ): void {
    if (path.length < 1) {
      throw new Error('Tried to delete an empty path!');
    } else {
      const filename = path[path.length - 1];

      if (this.confirmationModal.current == null) {
        throw new Error('Tried to delete file before UI was ready!.');
      } else {
        this.confirmationModal.current.ask(
          `Do you really want to delete ${filename}`,
          () => {
            // This string composition is necessary because path contains only the path within a project.
            ProjectManagement.deleteOverall(
              `${projectName}/${path.join('/')}`
            ).then(response => {
              // The response contains the new file structure, where the choosen file it deleted.
              this.showProject(response);
              // if the deleted file is the opened one, empty the editor
              if (path.join('/') === currentlyOpenFile.join('/')) {
                this.setText('');
                this.setOpenedPath([]);
              }
            });
          }
        );
      }
    }
  }

  /*
   * delete projects from server
   * the main difference from deleteFile is that the path to delete is composed differently
   */
  public deleteProject(projectName: string, path: string): void {
    // Show a dialog to confirm the deletion of the project
    if (this.confirmationModal.current == null) {
      throw new Error('Tried to delete file before UI was ready!.');
    } else {
      this.confirmationModal.current.ask(
        `Really delete project ${path}?`,
        // Called when the dialog was confirmed
        () => {
          ProjectManagement.deleteOverall(path); // Project to delete, in this case always the project that was opened
          if (path === projectName) {
            this.showProject({});
            this.setText('');
            this.setOpenedPath([]);
          }
        }
        // Nothing happens when the dialog was canceled
      );
    }
  }

  /*
   * create file/folder/project on the server. Files have type == file.
   * Projects/folders have type == folder
   * only used internally
   */
  private static createOverall(
    path: string,
    type: FileFolderEnum
  ): Promise<Project> {
    const escapedPath = escape(path);

    const url = `${serverAddress}/projects/${escapedPath}?type=${type}`;
    return fetch(url, {
      method: 'PUT',
      mode: 'cors',
    }).then(response => response.json());
  }

  /*
   * create a file in the active project
   */
  public createFile(
    projectName: string,
    path: string[],
    type: FileFolderEnum
  ): void {
    const file = prompt('Enter Name', '');

    if (file !== null && !file.includes('/')) {
      path.push(file);
      const requestPath = `${projectName}/${path.join('/')}`;

      ProjectManagement.createOverall(requestPath, type).then(response => {
        this.showProject(response);

        if (type !== 'folder') {
          this.openFile(path);
        }
      });
    } else if (file !== null && file.includes('/')) {
      alert('No appropriate filename. Filename includes: / ');
    }
  }

  /*
   * create a new project
   * the main difference from createFile is that the path is composed differently
   */

  public createProject(): void {
    const file = prompt('Enter Name', '');
    if (file !== null && !file.includes('/')) {
      ProjectManagement.createOverall(file, FileFolderEnum.folder).then(
        response => {
          this.projectController
            .openProject(file)
            .catch(e => {
              console.error(
                'Creating the project failed, because we could not sync with the server'
              );

              console.error(e);
            })
            .then(() => {
              this.showProject(response);
              this.setText('');
              this.setOpenedPath([]);
            });
        }
      );
    }
    if (file !== null && file.includes('/')) {
      alert('No appropriate filename. Filename includes: / ');
    }
  }

  public runProof(path: string): Promise<ProofResults> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    const url = `${serverAddress}/proof/${escapedPath}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        // 'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => response.json()); // parse the response body as json};
  }

  /*
   * This function updates the filename of the given resource path.
   * The new filename is entered by the prompt, which is created
   * inside the fuction.
   *
   */
  public updateFileName(path: string[]): void {
    const name = prompt('Enter Name', '');

    if (name !== '..' && name !== '.' && name !== null && !name.includes('/')) {
      // Path to the ressource we want to rename
      // TODO: Handle if project not set
      const url = `${serverAddress}/projects/${
        (this.getCurrentProject() as Project).name
      }/${path.join('/')}`;

      // Remove the current filename from the path array
      // and then create path for the renamed ressource:
      const oldfilename = path.pop();
      const renamedRes = `/projects/${
        (this.getCurrentProject() as Project).name
      }/${path.join('/')}/${name}`;

      // Create a new array with the modify openPath
      const newOpenPath = path.concat([name]);

      const requestbody = {
        fileName: renamedRes,
      };

      fetch(url, {
        method: 'POST',
        mode: 'cors',
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(requestbody), // necessary if you want to send a JSON object in a fetch request
      }).then(response =>
        response.json().then(res => {
          this.showProject(res);
          // If set openedPath isn't set after renaming, the currently openedFile would not math
          // to the openedPath.
          this.setOpenedPath(newOpenPath);

          if (path[path.length - 1] === oldfilename) {
            this.setFileName(name);
          }
        })
      );
    }
    if (name !== null && name.includes('/')) {
      alert('No appropriate filename. Filename includes: /');
    }
    if (name === '..' || name === '.') {
      alert('No appropriate filename. Cannot be .. or .');
    }
  }

  /**
   * That function makes a call to the HTTP rest controller
   * and updates the content of the file specified by the
   * parameters.
   *
   * @param path to the file that will be updated
   * @param content that will be set to the file
   */
  public updateFileContent(path: string[], content: string): Promise<void> {
    // Path to the ressource we want to save
    // TODO: Check if project exists
    const url = `${serverAddress}/projects/${
      (this.getCurrentProject() as Project).name
    }/${path.join('/')}`;

    const requestbody = {
      fileContent: content,
    };

    return fetch(url, {
      method: 'POST',
      mode: 'cors',
      headers: {
        Accept: 'application/json',
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestbody), // necessary if you want to send a JSON object in a fetch request
    }).then(response => {
      if (response.status !== 200) {
        alert(
          'Uups! Something went wrong while saving your filecontent to the server'
        );
      }
    });
  }
}
