import React, { RefObject, ReactSVG } from 'react';
import PropTypes from 'prop-types';
import 'bootstrap/dist/css/bootstrap.css';
import NotificationSystem from 'react-notification-system';
import '../index.css';
import Usernames from './user-names/user-names';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome';
import {
  faForward,
  faBoxOpen,
  faStarOfLife,
  faDownload,
  faCloudUploadAlt,
  faSave,
  faBomb,
  faTrashAlt,
  faTag,
  faDirections,
} from '@fortawesome/free-solid-svg-icons';

import {
  Navbar,
  NavbarBrand,
  Nav,
  UncontrolledDropdown,
  DropdownToggle,
  DropdownMenu,
  DropdownItem,
} from 'reactstrap';

import { OpenModal, DeleteModal, MacroModal } from './selection-modals.jsx';

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
    this.toggleMacroModal = this.toggleMacroModal.bind(this);
    this.openProjectOnClick = this.openProjectOnClick.bind(this);
    this.openFileOnClick = this.openFileOnClick.bind(this);
    this.downloadFileOnClick = this.downloadFileOnClick.bind(this);
    this.state = {
      showOpenModal: false,
      showDeleteModal: false,
      showMacroModal: false,
    };
  }

  private toggleOpenModal(): void {
    this.setState({ showOpenModal: !this.state.showOpenModal });
  }

  private toggleDeleteModal(): void {
    this.setState({ showDeleteModal: !this.state.showDeleteModal });
  }

  /**
   * Inverts the visibility of the modal that selects macro files
   */
  private toggleMacroModal(): void {
    this.setState({ showMacroModal: !this.state.showMacroModal });
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
          <NavbarBrand style={{ color: 'white' }}>KollaborierbaR</NavbarBrand>
          <Nav className="ml-auto" navbar>
            <Usernames />

            <UncontrolledDropdown>
              <DropdownToggle nav caret>
                KeY
              </DropdownToggle>
              <DropdownMenu right>
                <DropdownItem
                  onClick={() => {
                    this.props.saveFile().then(() => this.props.onProveFile());
                  }}
                >
                  <FontAwesomeIcon
                    icon={faForward}
                    style={{ marginRight: '0.5em' }}
                  />
                  Prove all contracts
                </DropdownItem>
                <DropdownItem onClick={this.toggleMacroModal}>
                  <FontAwesomeIcon
                    icon={faDirections}
                    style={{ marginRight: '0.5em' }}
                  />
                  Select Macro
                </DropdownItem>
              </DropdownMenu>
            </UncontrolledDropdown>

            <UncontrolledDropdown>
              <DropdownToggle nav caret>
                Project
              </DropdownToggle>
              <DropdownMenu right>
                <DropdownItem onClick={this.props.onCreateProject}>
                  <FontAwesomeIcon
                    icon={faStarOfLife}
                    style={{ marginRight: '0.5em' }}
                  />
                  Create project
                </DropdownItem>
                <DropdownItem onClick={this.toggleOpenModal}>
                  <FontAwesomeIcon
                    icon={faBoxOpen}
                    style={{ marginRight: '0.5em' }}
                  />
                  Open project
                </DropdownItem>
                <DropdownItem onClick={this.toggleDeleteModal}>
                  <FontAwesomeIcon
                    icon={faBomb}
                    style={{ marginRight: '0.5em' }}
                  />
                  Delete project
                </DropdownItem>
              </DropdownMenu>
            </UncontrolledDropdown>
            <OpenModal
              isOpen={this.state.showOpenModal}
              toggle={this.toggleOpenModal}
              selectOperation={this.props.onOpenProject}
            />
            <DeleteModal
              isOpen={this.state.showDeleteModal}
              toggle={this.toggleDeleteModal}
              selectOperation={this.props.onDeleteProject}
            />
            <MacroModal
              isOpen={this.state.showMacroModal}
              toggle={this.toggleMacroModal}
              loadFunction={this.props.getMacroFiles}
              selectOperation={this.props.onSelectMacro}
            />
            <UncontrolledDropdown>
              <DropdownToggle nav caret>
                File
              </DropdownToggle>
              <DropdownMenu right>
                <DropdownItem onClick={this.downloadFileOnClick}>
                  <FontAwesomeIcon
                    icon={faDownload}
                    style={{ marginRight: '0.5em' }}
                  />
                  Download
                </DropdownItem>
                <DropdownItem onClick={this.openFileOnClick}>
                  <FontAwesomeIcon
                    icon={faCloudUploadAlt}
                    style={{ marginRight: '0.5em' }}
                  />
                  Upload
                </DropdownItem>
                <DropdownItem onClick={this.props.onDeleteFile}>
                  <FontAwesomeIcon
                    icon={faTrashAlt}
                    style={{ marginRight: '0.5em' }}
                  />
                  Delete
                </DropdownItem>
                <DropdownItem onClick={this.props.onUpdateFileName}>
                  <FontAwesomeIcon
                    icon={faTag}
                    style={{ marginRight: '0.5em' }}
                  />
                  Rename
                </DropdownItem>
                <DropdownItem onClick={this.props.saveFile}>
                  <FontAwesomeIcon
                    icon={faSave}
                    style={{ marginRight: '0.5em' }}
                  />
                  Save
                </DropdownItem>
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
          href={`data:text/plain;charset=utf-8, ${encodeURIComponent(
            this.props.text
          )}`}
          download={
            this.props.getFilePath()[this.props.getFilePath().length - 1]
          }
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

// defining the structure of the state
interface State {
  showOpenModal: boolean;
  showDeleteModal: boolean;
  showMacroModal: boolean;
}

// define the structure received KeY results
interface ProofResults {
  succeeded: string[];
  failed: string[];
  errors: string[];
}

// defining the structure of this react components properties
interface Props {
  getMacroFiles: any;
  getFilePath: () => string[];
  text: string;
  setText(text: string): void;
  onDeleteFile(): void;
  onDeleteProject(): void;
  onUpdateFileName(): void;
  saveFile(): Promise<void>;
  onOpenProject(): void;
  onCreateProject(): void;
  onProveFile(): void;
  onSelectMacro(macro: string): void;
  notificationSystem: React.RefObject<NotificationSystem.System>;
}
