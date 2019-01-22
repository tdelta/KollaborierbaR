import NotificationSystem from 'react-notification-system';

import {serverAddress} from './constants';
import ConfirmationModal from './components/confirmation-modal';

import {Network, ProjectEvent, RenamedFileEvent, ProjectFileEvent, ProjectEventType} from './network';

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

enum FileFolderEnum {
    file = 'file',
    folder = 'folder'
}

interface FileOrFolder {
    name: string;
    type: FileFolderEnum;
    contents?: FileOrFolder[];
}

interface Project {
    name: string;
    contents: FileOrFolder[];
}

interface EmptyObject {}

export default class ProjectManagement {
    private showProject: (p: Project | EmptyObject) => void;
    private getCurrentProject: () => Project | EmptyObject;
    private setText: (s: string) => void;
    private getFileName: () => string | undefined;
    private setFileName: (name: string | undefined) => void;
    private getOpenedPath: () => string[];
    private setOpenedPath: (path: string[]) => void;
    private confirmationModal: React.RefObject<ConfirmationModal>;
    private notificationSystem: React.RefObject<NotificationSystem.System>;
    private openFile: (path: string[]) => void;
    private network: Network;

    constructor(
        showProject: (p: Project | EmptyObject) => void,
        getCurrentProject: () => Project | EmptyObject,
        setText: (s: string) => void,
        getFileName: () => string | undefined,
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
        this.getFileName = getFileName;
        this.setFileName = setFileName;
        this.getOpenedPath = getOpenedPath;
        this.setOpenedPath = setOpenedPath;
        this.confirmationModal = confirmationModal;
        this.notificationSystem = notificationSystem;
        this.openFile = openFile;

        this.network = new Network({
            onProjectEvent: (event: ProjectEvent | RenamedFileEvent | ProjectFileEvent) => {
                const currentProject = this.getCurrentProject();

                switch (event.eventType) {
                    case ProjectEventType.DeletedFile:
                        this.openProject(
                            (<Project>currentProject).name,
                            false
                        );

                        if (
                            !ProjectManagement.projectContainsPath(
                                (<Project>currentProject),
                                this.getOpenedPath()
                            )
                        ) {
                            this.setText('');
                            this.setFileName(undefined);
                        }

                        if (this.notificationSystem.current) {
                            this.notificationSystem.current.clearNotifications();
                            this.notificationSystem.current.addNotification({
                                message: 'A file got deleted',
                                level: 'error',
                                position: 'bc'
                            });
                        }
                        
                        break;
                    case ProjectEventType.RenamedFile:
                        this.openProject(
                            (<Project>currentProject).name,
                            false
                        );

                        const renameEvent: RenamedFileEvent = (<RenamedFileEvent> event);

                        if (renameEvent.originalPath === this.getOpenedPath().join('/')) {
                            // TODO: Evtl abstimmen mit Collab controller
                            const newPathArray: string[] = renameEvent.newPath.split('/');

                            if (newPathArray.length < 1) {
                                console.log('Error: Updated file path is invalied.');
                            }

                            else {
                                this.setFileName(newPathArray[newPathArray.length - 1]);
                                this.setOpenedPath(newPathArray);
                            }
                        }

                        if (this.notificationSystem.current) {
                            this.notificationSystem.current.clearNotifications();
                            this.notificationSystem.current.addNotification({
                                message: `File ${renameEvent.originalPath} got renamed to ${renameEvent.newPath}.`,
                                level: 'info',
                                position: 'bc'
                            });
                        }
                        
                        break;
                    case ProjectEventType.UpdatedFile:
                        const fileEvent: ProjectFileEvent = (<ProjectFileEvent> event);

                        if (fileEvent.filePath === this.getOpenedPath().join('/')) {
                            if (this.notificationSystem.current) {
                                this.notificationSystem.current.clearNotifications();
                                this.notificationSystem.current.addNotification({
                                    message: `Permanently saved the contents of your currently opened file.`,
                                    level: 'success',
                                    position: 'bc'
                                });
                            }
                        }
                        
                        break;
                    case ProjectEventType.DeletedProject:
                        this.showProject({});
                        this.setText('');
                        this.setFileName(undefined);

                        if (this.notificationSystem.current) {
                            this.notificationSystem.current.clearNotifications();
                            this.notificationSystem.current.addNotification({
                                message: 'Your project got deleted.',
                                level: 'error',
                                position: 'bc'
                            });
                        }
                        
                        break;
                    case ProjectEventType.UpdatedProject:
                        if (!((<any>currentProject).name == null || (<any>currentProject).contents == null)) {
                            this.openProject(
                                (<Project>currentProject).name,
                                false
                            );

                            if (
                                !ProjectManagement.projectContainsPath(
                                    (<Project>currentProject),
                                    this.getOpenedPath()
                                )
                            ) {
                                this.setText('');
                                this.setFileName(undefined);
                            }
                        }

                        if (this.notificationSystem.current) {
                            // TODO evtl. nicht alle Notifications entfernen
                            this.notificationSystem.current.clearNotifications();
                            this.notificationSystem.current.addNotification({
                                message: 'The project files got updated.',
                                level: 'info',
                                position: 'bc'
                            });
                        }

                        break;
                }
            },

            onConnect: () => undefined
        });
      }
    
    public getNetwork(): Network{
      return this.network;
    }

    private static projectContainsPath(project: Project, path: string[]): boolean {
        const contentRecursion = (file: FileOrFolder, path: string[]): boolean => {
            if (path.length < 1) {
                return false;
            }

            else if (path.length === 1) {
                return file.name === path[0];
            }

            else if (file.contents == null) {
                return false;
            }

            else {
              return file.contents.some(
                (file) => contentRecursion(file, path.slice(1))
              );
            }
        };

        return project.contents.some(
            (file) => contentRecursion(file, path)
        );
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
        path = escape(path);
        // API URL of the server we will use for our request
        const url = serverAddress + '/projects/' +path;

        return fetch(url, {
            method: 'GET',
            mode: 'cors', // enable cross origin requests. Server must also allow this!
            headers: {
                'Accept' : 'application/json', // we want a json object back
                //'Content-Type': 'application/json', // we are sending a json object
            },
        })
            .then((response) =>  response.json()); // parse the response body as json
    }

    /*
     * load the list of available projects from the server
     */
    public static getProjects(): Promise<string[]> {
        const url = serverAddress + '/projects';
        return fetch(url, {
            method: 'GET',
            mode: 'cors',
            headers: {
                'Accept': 'application/json',
            },
        })
            .then((response) => response.json());
    }


    /*
     * load the related files for the project with name 'name' from the server
     * the handler displays the returned project in the editor
     */
    public openProject(name: string, resetFile: boolean | undefined): void {
        if (resetFile == null) {
            resetFile = true;
        }

        const escapedName = escape(name);
        
        const url = serverAddress + '/projects/'+ escapedName;

        this.closeProject(
            () => 
                this.network.openProject(
                    name,
                    () => 
                        fetch(url, {
                            method: 'GET',
                            mode: 'cors',
                        })
                            .then((response) => {
                                response.json()
                                    .then((json: Project) => {
                                        this.showProject(json);

                                        if (resetFile) {
                                            this.setText('');
                                            this.setFileName(undefined);
                                        }
                                    
                                    });
                                //return {'status': response.status, 
                                //  'statusText': response.statusText};
                            }),
                    () => console.log("Could not sync with server to open project")
                )
        );
    }

    public closeProject(cb:() => void): void {
        const project = this.getCurrentProject();

        if ((<Project>project).name == null) {
            cb();
        }

        else {
            this.network.closeProject(
              (<Project>project).name,
              cb,
              () => {
                console.log('Failed to unsubscribe, you may still receive messages for your closed project');
                cb()
              }
            );
        }
    }

    /*
     * Calls the REST delete method. only used internally
     * TODO: Better explanation, what this method does
     */
    private static deleteOverall(path: string): Promise<Project | EmptyObject> {
        path = escape(path);
        const url = serverAddress + '/projects/' +  path;

        return fetch(url, {
            method: 'DELETE',
            mode: 'cors', // enable cross origin requests. Server must also allow this!
            headers: {
                'Accept' : 'application/json', // we want a json object back
            }
        })
            .then((response) =>  response.json()) // parse the response body as json
            .catch(() => {}); // if the json body is empty (e.g. after project delete) return an empty json object
    }

    /*
     * Deletes a file from the loaded project on the server
     */
    public deleteFile(currentlyOpenFile: string, projectName: string, path: string[]): void {
        if (path.length < 1) {
            throw new Error('Tried to delete an empty path!');
        }

        else {
            const filename = path[path.length - 1];

            if (this.confirmationModal.current == null) {
                throw new Error("Tried to delete file before UI was ready!.");
            }

            else {
              this.confirmationModal.current.ask(
                  'Do you really want to delete ' + filename,
                  () => {
                      // This string composition is necessary because path contains only the path within a project.
                      ProjectManagement.deleteOverall(projectName + '/' + path.join('/'))
                          .then((response) => {
                          // The response contains the new file structure, where the choosen file it deleted.
                              this.showProject(response);

                              // if the deleted file is the opened one, empty the editor
                              if (path[path.length-1] === currentlyOpenFile) {
                                  this.setText('');
                                  this.setFileName(undefined);
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
            throw new Error("Tried to delete file before UI was ready!.");
        }

        else {
            this.confirmationModal.current.ask(
                `Really delete project ${path}?`,
                // Called when the dialog was confirmed
                () => {
                    ProjectManagement.deleteOverall(path); // Project to delete, in this case always the project that was opened
                    if (path === projectName) {
                        this.showProject({});
                        this.setText('');
                        this.setFileName(undefined);
                    }
                },
                // Nothing happens when the dialog was canceled
            );
        }
    }


    /*
     * create file/folder/project on the server. Files have type == file. 
     * Projects/folders have type == folder
     * only used internally
     */
    private static createOverall(path: string, type: FileFolderEnum): Promise<Project> {
        path = escape(path);
        const url = serverAddress + '/projects/' + path + '?type=' + type;
        return fetch(url, {
            method: 'PUT',
            mode: 'cors',
        })
            .then((response) => response.json());
    }

    /*
     * create a file in the active project
     */
    public createFile(projectName: string, path: string[], type: FileFolderEnum): void {
        const file = prompt('Enter Name', '');

        if (file !== null && !file.includes("/")) {
            path.push(file);
            const requestPath = projectName + '/' + path.join('/');

            ProjectManagement.createOverall(requestPath, type)
                .then((response) => {
                    this.showProject(response);
                    this.openFile(path);
                });
        } else if(file !== null && file.includes('/')){
            alert('No appropriate filename. Filename includes: / ');
        }
    }


    /*
     * create a new project
     * the main difference from createFile is that the path is composed differently
     */ 
    public createProject(): void {
        const file = prompt('Enter Name', '');
        if (file !== null && !file.includes("/")) {
            ProjectManagement.createOverall(file, FileFolderEnum.folder)
                .then((response) => {
                    this.network.openProject(
                        file,
                        () => {
                            this.showProject(response);
                            this.setText('');
                            this.setFileName(undefined);
                        },
                        () => {
                            console.log('Creating the project failed, because we could not sync with the server');
                        }
                    );
                });
        }if(file !== null && file.includes("/")){
            alert('No appropriate filename. Filename includes: / ');
        }

    }

    public runProof(path: string): Promise<ProofResults> {
        path = escape(path);
        // API URL of the server we will use for our request
        const url = serverAddress + '/proof/' +path;

        return fetch(url, {
            method: 'GET',
            mode: 'cors', // enable cross origin requests. Server must also allow this!
            headers: {
                'Accept' : 'application/json', // we want a json object back
                //'Content-Type': 'application/json', // we are sending a json object
            },
        })
      .then((response) => response.json()); // parse the response body as json};
    }

    /*
     * updates the filename of the given resource path 
     *
     */
    public updateFileName(path: string[]): void {
        const name = prompt('Enter Name', '');

        if(name !== '..' && name !== '.' && name !== null && !name.includes('/')){

            // Path to the ressource we want to rename
            // TODO: Handle if project not set
            const url = serverAddress + '/projects/' + (<Project>this.getCurrentProject()).name + '/' +path.join('/');

            // Remove the current filename from the path array
            // and then create path for the renamed ressource:
            const oldfilename = path.pop();
            const renamedRes = '/projects/' + (<Project>this.getCurrentProject()).name + '/' + path.join('/') + '/' + name; 

            // Create a new array with the modify openPath
            const newOpenPath = path.concat([name]);
            
            const requestbody = {
                'fileName' : renamedRes
            };

            fetch(url, {
                method: 'POST',
                mode: 'cors', 
                headers: {
                    'Accept' : 'application/json',
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify(requestbody) // necessary if you want to send a JSON object in a fetch request
            })
                .then((response) =>  
                    response.json()
                        .then(res => {this.showProject(res);
                            // If set openedPath isn't set after renaming, the currently openedFile would not math
                            // to the openedPath.
                            this.setOpenedPath(newOpenPath);

                            if(this.getFileName() === oldfilename){
                                this.setFileName(name);
                            }})
                );

        } if(name !== null && name.includes('/')){
            alert('No appropriate filename. Filename includes: /');
        } if(name === '..' || name === '.'){
            alert('No appropriate filename. Cannot be .. or .');
        }
    }

    public updateFileContent(path: string[], content: string): void {
        // Path to the ressource we want to save
        // TODO: Check if project exists
      const url = serverAddress + '/projects/' + (<Project>this.getCurrentProject()).name + '/' +path.join('/');

        const requestbody = {
            'fileContent' : content
        };

        fetch(url, {
            method: 'POST',
            mode: 'cors',
            headers: {
                'Accept' : 'application/json',
                'Content-Type' : 'application/json'
            },
            body: JSON.stringify(requestbody) // necessary if you want to send a JSON object in a fetch request
        }).then((response) =>  {if(response.status !== 200) 
            alert('Uups! Something went wrong while saving your filecontent to the server');
        });
    }
}