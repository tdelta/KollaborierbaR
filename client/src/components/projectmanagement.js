/*
 * load the list of available projects from the server
 */
function getProjects() {
    var url = new URL('http://localhost:9000/projects');
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
    var url = new URL('http://localhost:9000/projects/'+ name);

    return fetch(url, {
        method: 'GET',
        mode: 'cors',
    })
        .then((response) => {
            response.json()
                .then((json) => this.showProject(json));
            return {'status': response.status, 
                'statusText': response.statusText};
        });
}


function deleteOverall(path){
    var url = 'http://localhost:9000/projects/' +  path;
    
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
                deleteOverall('/' + this.state.project.name + '/' + path.join('/'))
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
 */
function deleteProject(path) {
    // Show a dialog to confirm the deletion of the project
    this.confirmationModal.current.ask(
        `Really delete project ${path}?`,
        // Called when the dialog was confirmed
        () => {
            deleteOverall('/' + path); // Project to delete, in this case always the project that was opened
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
 */
function createOverall(path, type) {
    var url = 'http://localhost:9000/projects/' + path + '?type=' + type;

    return fetch(url, {
        method: 'PUT',
        mode: 'cors',
    })
        .then((response) => response.json());
}

function createFile(path, type) {
    let file = prompt('Enter Name', '');
    if (file !== null) {
        path.push(file);
        const requestPath = this.state.project.name + '/' + path.join('/');

        createOverall(requestPath, type)
            .then((response) => {
                this.showProject(response);
                this.openFile(path);
            });
    }
}

function createProject() {
    let file = prompt('Enter Name', '');
    if (file !== null) {

        createOverall(file, 'folder')
            .then((response) => {
                this.showProject(response);
                this.setText('');
                this.setFileName(undefined);
            });
    }
}


export {deleteFile, deleteProject, createFile, createProject, getProjects, openProject};
