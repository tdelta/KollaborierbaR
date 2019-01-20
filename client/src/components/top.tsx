import React, { RefObject, ReactSVG } from 'react';
import PropTypes from 'prop-types';

import 'bootstrap/dist/css/bootstrap.css';

import '../index.css';

import {
  Navbar,
  NavbarBrand,
  Nav,
  UncontrolledDropdown,
  DropdownToggle,
  DropdownMenu,
  DropdownItem,
} from 'reactstrap';

import {
    OpenModal, 
    DeleteModal
} from './project-modals.jsx';

import {
    createFile,
} from './projectmanagement.js';


export default class Top extends React.Component<Props, State> {
  private fileSelector: RefObject<HTMLInputElement>;
  private downloadSelector: RefObject<HTMLInputElement>;
  private fileReader?: FileReader;

  constructor(props: Props) {
    super(props);
    this.fileSelector = React.createRef();
    this.downloadSelector = React.createRef();
    this.onFileChosen = this.onFileChosen.bind(this);
    this.onFileLoaded = this.onFileLoaded.bind(this);
    this.toggleOpenModal = this.toggleOpenModal.bind(this);
    this.toggleDeleteModal = this.toggleDeleteModal.bind(this);
    this.openProjectOnClick = this.openProjectOnClick.bind(this);
    this.openFileOnClick = this.openFileOnClick.bind(this);
    this.downloadFileOnClick = this.downloadFileOnClick.bind(this);
    this.state = {
      showOpenModal: false,
      showDeleteModal: false
    };
  }

  private toggleOpenModal(): void {
    this.setState({ showOpenModal: !this.state.showOpenModal });
  }

  private toggleDeleteModal(): void {
    this.setState({ showDeleteModal: !this.state.showDeleteModal });
  }

  private onFileChosen(event: HTMLInputEvent): void {
    this.fileReader = new FileReader();
    this.fileReader.onloadend = this.onFileLoaded;

    if (event.target != null && event.target.files != null) {
      this.fileReader.readAsText(event.target.files[0]);
    }
  }

  private onFileLoaded(): void {
    if (this.fileReader != null && typeof this.fileReader.result === 'string') {
      this.props.setText(this.fileReader.result);
    }
  }

  private openProjectOnClick(): void {
    if (this.fileSelector.current != null) {
      this.fileSelector.current.click();
    }
  }

  private downloadFileOnClick(): void {
    if (this.downloadSelector.current != null) {
      this.downloadSelector.current.click();
    }
  }

  private openFileOnClick(): void {
    if (this.fileSelector.current != null) {
      this.fileSelector.current.click();
    }
  }

  public render() {
    return (
      <div>
        <Navbar color="dark" dark expand="md">
          <NavbarBrand href="/">KollaborierbaR</NavbarBrand>
          <Nav className="ml-auto" navbar>
            <UncontrolledDropdown>
              <DropdownToggle nav caret>
                Project
              </DropdownToggle>
              <DropdownMenu right>
                <DropdownItem onClick={this.toggleOpenModal}>
                  Open project
                </DropdownItem>
                <DropdownItem onClick={this.toggleDeleteModal}>
                  Delete project
                </DropdownItem>
                <DropdownItem onClick={this.props.onCreateProject}>
                  Create project
                </DropdownItem>
              </DropdownMenu>
            </UncontrolledDropdown>
            <OpenModal
              isOpen={this.state.showOpenModal}
              toggle={this.toggleOpenModal}
              projectOperation={this.props.onOpenProject}
            />
            <DeleteModal
              isOpen={this.state.showDeleteModal}
              toggle={this.toggleDeleteModal}
              projectOperation={this.props.onDeleteProject}
            />
            <UncontrolledDropdown>
              <DropdownToggle nav caret>
                File
              </DropdownToggle>
              <DropdownMenu right>
                <DropdownItem onClick={this.downloadFileOnClick}>Download</DropdownItem>
                <DropdownItem onClick={this.openFileOnClick}>Upload</DropdownItem>
                <DropdownItem onClick={this.props.onDeleteFile}>Delete</DropdownItem>
                <DropdownItem onClick={this.props.onUpdateFileName}>Rename</DropdownItem>
                <DropdownItem onClick={this.props.onUpdateFileContent}>Save</DropdownItem>
              </DropdownMenu>
            </UncontrolledDropdown>
          </Nav>
        </Navbar>

        <input
          type="file"
          id="file"
          ref={this.fileSelector}
          style={{ display: 'none' }}
          onChange={this.onFileChosen}
        />

        <a
          href={
            'data:text/plain;charset=utf-8,$(encodeURIComponent(this.props.text))'
          }
          download="test.txt"
        >
          <input
            type="button"
            ref={this.downloadSelector}
            style={{ display: 'none' }}
          />
        </a>
      </div>
    );
  }
}

// defining HTMLInput Event
interface HTMLInputEvent extends React.FormEvent<HTMLInputElement> {
  target: HTMLInputElement & EventTarget;
}

// defining the strcuture of the state
interface State {
  showOpenModal: boolean;
  showDeleteModal: boolean;
}

// defining the structure of this react components properties
interface Props {
  text: string;
  setText(text: string): void;
  showProject(project: object): void;
  onDeleteFile(): void;
  onDeleteProject(): void;
  onUpdateFileName(): void;
  onUpdateFileContent(): void;
  onOpenProject(): void;
  onCreateProject(): void;
}
