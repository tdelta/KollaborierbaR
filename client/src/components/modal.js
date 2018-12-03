/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import { ListGroup, ListGroupItem, Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

/*
 * load the list of availlablle projects from the server
 */
function getProjects() {
    var url = new URL('http://localhost:9000/projects/listProjects');
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
 */
function getProjectStructure(name) {
    var url = new URL('http://localhost:9000/projects/showProject');

    const params = {'name': name};

    url.search = new URLSearchParams(params);

    return fetch(url, {
        method: 'GET',
        mode: 'cors',
        headers: {
            'Accept': 'application/json',
        },
    })
        .then((response) => response.json());
}

class ModalSelect extends React.Component {
    constructor(props) {
        super(props);
        this.select = this.select.bind(this);
        this.loadProjectFiles = this.loadProjectFiles.bind(this);
        this.loadProjectNames = this.loadProjectNames.bind(this);
        this.listProjects = this.listProjects.bind(this);
        this.state = {
            projects: [],
            selected: {
                'id': -1,
                'name': ''
            }
        };
    }

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
     * loads the files for the selected project when the select button is pressed
     * through the setStructure props method the structure starts its long journey to the sidebar
     */
    loadProjectFiles() {
        let name = this.state.selected.name;
        if (name) {
            getProjectStructure(this.state.selected.name)
                .then((response) => this.props.setStructure(response));
            this.props.toggle();
        }
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
                    onClosed={() => this.select(-1, '')} className={this.props.className}
                >
                    <ModalHeader toggle={this.props.toggle}>Select Project</ModalHeader>
                    {/* the style enables a scrollbar, when the project names don't fit on the screen (100vh) with a 210 pixels margin */}
                    <ModalBody style={{'maxHeight': 'calc(100vh - 210px)', 'overflowY': 'auto'}}>
                        {/* generate the listed project names dynamically */}
                        {this.listProjects()}
                    </ModalBody>
                    <ModalFooter>
                        <Button color="primary" onClick={this.loadProjectFiles}>Select</Button>
                        <Button color="secondary" onClick={this.props.toggle}>Cancel</Button>
                    </ModalFooter>
                </Modal>
            </div>
        );
    }

}

export default ModalSelect;
