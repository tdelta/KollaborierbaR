/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import { ListGroup, ListGroupItem, Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

function getProjects() {
    var url = new URL('http://localhost:8080/projects/listProjects');
    return fetch(url, {
        method: 'GET',
        mode: 'cors',
        headers: {
            'Accept': 'application/json',
        },
    })
        .then((response) => response.json());

}

function getProjectStructure(name) {
    var url = new URL('http://localhost:8080/projects/showProject');

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
        this.project = [];
        this.loadProject = this.loadProject.bind(this);
        this.state = {
            projects: []
        };
    }

    // if selected to fast it is possible that no project is loaded, change!
    loadStructure(name) {
        getProjectStructure(name)
            .then((response) => this.project = response);
    }

    loadProject() {
        this.props.setStructure(this.project);
        this.props.toggle();
    }

    listProjects() {
        // check, whether there are any projects to list
        if (this.state.projects && this.state.projects.length > 0) {
            return (
                <ListGroup>
                    {
                        this.state.projects.map((name, i) => 
                            // key not necessary but added for good practice. see: https://reactjs.org/docs/lists-and-keys.html
                            <ListGroupItem key={i} onClick={() => this.loadStructure(name)} action>{name}</ListGroupItem>
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
                <Modal isOpen={this.props.isOpen} toggle={this.props.toggle} className={this.props.className}>
                    <ModalHeader toggle={this.props.toggle}>Select Project</ModalHeader>
                    <ModalBody>
                        {this.listProjects()}
                    </ModalBody>
                    <ModalFooter>
                        <Button color="primary" onClick={this.loadProject}>Select</Button>{' '}
                        <Button color="secondary" onClick={this.props.toggle}>Cancel</Button>
                    </ModalFooter>
                </Modal>
            </div>
        );
    }

    // right now this is only called once
    componentDidMount() {
        getProjects()
            .then((projects) => {this.setState({projects: projects});
            });
    }
}

export default ModalSelect;
