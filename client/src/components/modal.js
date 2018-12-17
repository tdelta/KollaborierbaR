/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import { ListGroup, ListGroupItem, Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

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
function openProject(name, handler) {
    var url = new URL('http://localhost:9000/projects/'+ name);

    return fetch(url, {
        method: 'GET',
        mode: 'cors',
    })
        .then((response) => {
            response.json()
                .then((json) => handler(json));
            return {'status': response.status, 
                'statusText': response.statusText};
        });
}

/*
 * delete projects from server
 */
function deleteProject(name, handler, previous) {
    var url = 'http://localhost:9000/projects/' + name;

    return fetch(url, {
        method: 'DELETE',
        mode: 'cors',
    })
        .then((response) => {
            // when the currently loaded project is deleted, delete the loaded files
            // aka set an empty json object
            if (previous === name && response.status === 200) {
                handler({});
            }
            return {'status': response.status, 
                'statusText': response.statusText};
        })
}

 
function deleteFile(path){
    var url = 'http://localhost:9000/projects/' +  path;
    
    return fetch(url, {
        method: 'DELETE',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
            'Accept' : 'application/json', // we want a json object back
        }
    })
        .then((response) =>  response.json()); // parse the response body as json
}

/*
 * create file/folder/project on the server. Files have type == file. 
 * Projects/folders have type == folder
 */
function createFile(name, type) {
    var url = 'http://localhost:9000/projects/' + name + "?type=" + type;

    return fetch(url, {
        method: 'PUT',
        mode: 'cors',
    })
        .then((response) => response.json());
}

/*
 * open project dialog window, that shows a list with available projects
 */
class ModalSelect extends React.Component {
    constructor(props) {
        super(props);
        this.select = this.select.bind(this);
        this.projectAction = this.projectAction.bind(this);
        this.loadProjectNames = this.loadProjectNames.bind(this);
        this.listProjects = this.listProjects.bind(this);
        this.state = {
            projects: [],
            selected: {
                'id': -1,
                'name': ''
            },
        };
    }

    /*
     * Static class variable that holds the name of the previously selected project
     * when a new one is selected. Is used to detected if the deleted project 
     * is the loaded project
     */
    static previous = "";
  
    /*
     * update the state with the selected project
     */
    select(name, id) {
        this.setState({
            'selected': {
                'id': id,
                'name': name
            }
        });
    }

    /*
     * loads the project list, called whenever the modal is opened
     */
    loadProjectNames() {
        getProjects()
            .then((projects) => {this.setState({projects: projects});
            });
    }

    /*
     * performs the esired operation for the selected project when the select button is pressed
     * through the setStructure props method the structure starts its long journey to the sidebar
     */
    projectAction() {
        let name = this.state.selected.name;
        if (name) {
            this.props.projectOperation(this.state.selected.name, this.props.setStructure, ModalSelect.previous)
            this.props.toggle();
            ModalSelect.previous = this.state.selected.name;
        }
    }

    /*
     * generates  JSX items for each project name
     */
    listProjects() {
        // check, whether there are any projects in list
        if (this.state.projects && this.state.projects.length > 0) {
            return (
                <ListGroup>
                    {
                        // the id is an enumeration for the projects and used to check with project entry is active
                        this.state.projects.map((name, id) => 
                            <ListGroupItem
                                key={id}
                                onClick={() => {this.select(name, id);}}
                                active={this.state.selected.id === id}
                            >
                                {name}
                            </ListGroupItem>
                        )
                    }
                </ListGroup>
            );
        }

        // if there arent any, inform the user about it
        else {
            return (
                <>
                    There are no projects on the server
                </>
            );
        }
    }

    render() {
        return (
            <div>
                {/*  
                  * onOpened: reload the project list   
                  * onClosed: when the modal is closed set the selected state to an invalid index, so that on a reopen no projects are highlighted
                  */}
                <Modal isOpen={this.props.isOpen} toggle={this.props.toggle} onOpened={() => this.loadProjectNames()} 
                    onClosed={() => this.select('', -1)} className={this.props.className}
                >
                    <ModalHeader toggle={this.props.toggle}>{'Select Project ' + this.props.usecase}</ModalHeader>
                    {/* the style enables a scrollbar, when the project names don't fit on the screen (100vh) with a 210 pixels margin */}
                    <ModalBody style={{'maxHeight': 'calc(100vh - 210px)', 'overflowY': 'auto'}}>
                        {/* generate the listed project names dynamically */}
                        {this.listProjects()}
                    </ModalBody>
                    <ModalFooter>
                        {/* projectAction is a prop and defines what to do with a project (e.g. deletion) */}
                        <Button color="primary" onClick={this.projectAction}>Select</Button>
                        <Button color="secondary" onClick={this.props.toggle}>Cancel</Button>
                    </ModalFooter>
                </Modal>
            </div>
        );
    }

}

/*
 * No inheritance from ModalSelect because it is considered bad practice in React.
 * See https://reactjs.org/docs/composition-vs-inheritance.html
 */
function OpenModal(props) {
    return (
        <ModalSelect {...props} projectOperation={openProject} usecase="To Open" />
    );
}

function DeleteModal(props) {
    return (
        <ModalSelect {...props} projectOperation={deleteProject} usecase="To Delete"/>
    );
}

export {OpenModal, DeleteModal, deleteFile, createFile};
