import React from 'react';
import PropTypes from 'prop-types';

import 'bootstrap/dist/css/bootstrap.css';

import './index.css';

import {
    Navbar,
    NavbarBrand,
    Nav,
    UncontrolledDropdown,
    DropdownToggle,
    DropdownMenu,
    DropdownItem } from 'reactstrap';

import ModalSelect from './modal.js';

export default class Top extends React.Component {
    constructor(props) {
        super(props);
        this.fileSelector = React.createRef();
        this.downloadSelector = React.createRef();
        this.onFileChosen = this.onFileChosen.bind(this);
        this.onFileLoaded = this.onFileLoaded.bind(this);
        this.toggleModal = this.toggleModal.bind(this);
        this.state = {
            showModal: false
        };
    }

    toggleModal() {
        this.setState({ showModal: !this.state.showModal });
    }
     
    onFileChosen(event){
        this.fileReader = new FileReader();
        this.fileReader.onloadend = this.onFileLoaded;
        this.fileReader.readAsText(event.target.files[0]);
    }

    onFileLoaded() {
        this.props.setText(this.fileReader.result);
    }

    render() {
        return(
            <div>
                <Navbar color="dark" dark expand="md">
                    <NavbarBrand href="/">KollaborierbaR</NavbarBrand>
                    <Nav className="ml-auto" navbar>
                        <UncontrolledDropdown >
                            <DropdownToggle nav caret>
                                Project
                            </DropdownToggle>
                            <DropdownMenu right>
                                <DropdownItem onClick={this.toggleModal}>
                                    Open project
                                </DropdownItem>
                                <DropdownItem onClick={() => this.fileSelector.current.click()}>
                                    Create project
                                </DropdownItem>
                            </DropdownMenu>
                        </UncontrolledDropdown>
                        <ModalSelect
                            isOpen={this.state.showModal}
                            toggle={this.toggleModal}
                            setStructure={this.props.showProject}
                        />
                        <UncontrolledDropdown>
                            <DropdownToggle nav caret>
                                File
                            </DropdownToggle>
                            <DropdownMenu right>
                                <DropdownItem onClick={() => this.downloadSelector.current.click()}>
                                    Save
                                </DropdownItem>
                                <DropdownItem onClick={() => this.fileSelector.current.click()}>
                                    Load
                                </DropdownItem>
                            </DropdownMenu>
                        </UncontrolledDropdown>
                    </Nav>
                </Navbar>

                <input
                    type="file"
                    id="file"
                    ref={this.fileSelector}
                    style={{display: 'none'}}
                    onChange={this.onFileChosen}
                />
                
                <a
                    href={'data:text/plain;charset=utf-8,'+ encodeURIComponent(this.props.text)}
                    download="test.txt"
                >
                    <input type="button" ref={this.downloadSelector} style={{display: 'none'}}/>
                </a>
            </div>
        );
    }
}

Top.propTypes = {
    setText: PropTypes.func.isRequired,
    text: PropTypes.string,
    showProject: PropTypes.func
};