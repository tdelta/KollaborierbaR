import {serverAddress} from '../constants.ts';

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
function openFile(path) { 
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

export default openFile;


/*
 * load the list of available projects from the server
 */
function getProjects() {
    var url = serverAddress + '/projects';
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
function openProject(name) {
    name = escape(name);
    
    var url = serverAddress + '/projects/'+ name;

    return fetch(url, {
        method: 'GET',
        mode: 'cors',
    })
        .then((response) => {
            response.json()
                .then((json) => {
                    this.showProject(json);
                    this.setText('');
                    this.setFileName(undefined);
                
                });
            //return {'status': response.status, 
            //  'statusText': response.statusText};
        });
}

/*
 * Calls the REST delete method. only used internally
 */
function deleteOverall(path){
    path = escape(path);
    var url = serverAddress + '/projects/' +  path;
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
function deleteFile(path){
    
    if (path.length < 1) {
        throw new Error('Tried to delete an empty path!');
    }

    else {
        const filename = path[path.length - 1];

        this.confirmationModal.current.ask(
            'Do you really want to delete ' + filename,
            () => {
                // This string composition is necessary because path contains only the path within a project.
                deleteOverall(this.state.project.name + '/' + path.join('/'))
                    .then((response) => {
                    // The response contains the new file structure, where the choosen file it deleted.
                        this.showProject(response);
                        // if the deleted file is the opened one, empty the editor
                        if (path[path.length-1] === this.state.filename) {
                            this.setText('');
                            this.setFileName(undefined);
                        }
                    });
            }
        );
    }

}


/*
 * delete projects from server
 * the main difference from deleteFile is that the path to delete is composed differently
 */
function deleteProject(path) { 
    // Show a dialog to confirm the deletion of the project
    this.confirmationModal.current.ask(
        `Really delete project ${path}?`,
        // Called when the dialog was confirmed
        () => {
            deleteOverall(path); // Project to delete, in this case always the project that was opened
            if (path === this.state.project.name) {
                this.showProject({});
                this.setText('');
                this.setFileName(undefined);
            }
        },
        // Nothing happens when the dialog was canceled
    );
}


/*
 * create file/folder/project on the server. Files have type == file. 
 * Projects/folders have type == folder
 * only used internally
 */
function createOverall(path, type) {
    path = escape(path);
    var url = serverAddress + '/projects/' + path + '?type=' + type;
    return fetch(url, {
        method: 'PUT',
        mode: 'cors',
    })
        .then((response) => response.json());
}

/*
 * create a file in the active project
 */
function createFile(path, type) {
    let file = prompt('Enter Name', '');
    if (file !== null && !file.includes("/")) {
        path.push(file);
        const requestPath = this.state.project.name + '/' + path.join('/');
        createOverall(requestPath, type)
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
function createProject() {
    let file = prompt('Enter Name', '');
    if (file !== null && !file.includes("/")) {
        createOverall(file, 'folder')
            .then((response) => {
                this.showProject(response);
                this.setText('');
                this.setFileName(undefined);
            });
    }if(file !== null && file.includes("/")){
        alert('No appropriate filename. Filename includes: / ');
    }

}


export {deleteFile, deleteProject, createFile, createProject, getProjects, openFile, openProject};
