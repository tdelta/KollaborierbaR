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
        this.state = {
            projects: []
        };
    }

    loadStructure(name) {
        getProjectStructure(name)
        .then((response) => console.log(response));
    }

    listProjects() {
        return (
                    this.state.projects.map((name, i) => 
                        // note: we add a key prop here to allow react to uniquely identify each
                        // element in this array. see: https://reactjs.org/docs/lists-and-keys.html
                        <ListGroupItem key={i} onClick={() => this.loadStructure(name)} action>{name}</ListGroupItem>)
                );
    }

    render() {
        return (
            <div>
                <Modal isOpen={this.props.isOpen} toggle={this.props.toggle} className={this.props.className}>
                    <ModalHeader toggle={this.props.toggle}>Select Project</ModalHeader>
                    <ModalBody>
                        <ListGroup>
                            {this.listProjects()}
                        </ListGroup>
                    </ModalBody>
                    <ModalFooter>
                        <Button color="primary" onClick={this.props.toggle}>Select</Button>{' '}
                        <Button color="secondary" onClick={this.props.toggle}>Cancel</Button>
                    </ModalFooter>
                </Modal>
            </div>
        );
    }

    componentDidMount() {
        getProjects()
            .then((projects) => {this.setState({projects: projects});
            });
    }
}

export default ModalSelect;
