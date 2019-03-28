import React from 'react';

import './app.css';

import NotificationSystem from 'react-notification-system';
import ErrorMessages from '../collaborative/ErrorMessages';
import Toggleable from './Toggleable.tsx';
import WelcomeScreen from './WelcomeScreen.tsx';
import Editor from './editor.tsx';
import Top from './top.tsx';
import Sidebar from './sidebar/Sidebar.tsx';
import ConfirmationModal from './confirmation-modal.tsx';
import Console from './console/Console.tsx';
import { StompService } from '../StompService';

import ProofsState from '../key/ProofsState';

import ProjectManagement from '../projectmanagement.ts';

import CollabController from '../collaborative/CollabController.ts';
import ConsoleSyncController from '../collaborative/ConsoleSyncController.ts';

import KeYInterface from '../key/KeYInterface.ts';

import { Button } from 'reactstrap';

/**
 * Main component of KollaborierbaR. Renders all other components (Editor etc.)
 * while holding global state.
 */
export default class App extends React.Component {
  constructor(props) {
    super(props);

    this.confirmationModal = React.createRef();
    this.notificationSystem = React.createRef();
    this.displayCloseButton = false;

    this.stompService = new StompService();

    this.projectManagement = new ProjectManagement(
      this.stompService,
      this.showProject.bind(this),
      () => this.state.project,
      this.setText.bind(this),
      this.setFileName.bind(this),
      () => this.state.openedPath,
      this.setOpenedPath.bind(this),
      this.confirmationModal,
      this.notificationSystem,
      this.openFile.bind(this)
    );

    // all methods should always refer to this instance of App, when
    // using the `this` variable.
    this.saveFile = this.saveFile.bind(this);
    this.setText = this.setText.bind(this);
    this.setDiagnostics = this.setDiagnostics.bind(this);
    this.setProvenObligations = this.setProvenObligations.bind(this);
    this.saveObligationResult = this.saveObligationResult.bind(this);
    this.deleteObligationResult = this.deleteObligationResult.bind(this);
    this.resetObligation = this.resetObligation.bind(this);
    this.proveFile = this.proveFile.bind(this);
    this.showProject = this.showProject.bind(this);
    this.openFile = this.openFile.bind(this);
    this.displaySequent = this.displaySequent.bind(this);
    this.closeSequent = this.closeSequent.bind(this);
    this.deleteFile = path =>
      this.projectManagement.deleteFile(
        this.state.openedPath,
        this.state.project.name,
        path
      );
    this.deleteProject = path =>
      this.projectManagement.deleteProject(this.state.project.name, path);
    this.createFile = (path, type) =>
      this.projectManagement.createFile(this.state.project.name, path, type);
    this.createProject = this.projectManagement.createProject.bind(
      this.projectManagement
    );
    this.openProject = this.projectManagement.openProject.bind(
      this.projectManagement
    );
    this.updateFileName = this.projectManagement.updateFileName.bind(
      this.projectManagement
    );
    this.updateFileContent = this.projectManagement.updateFileContent.bind(
      this.projectManagement
    );
    this.setConsoleVisibility = this.setConsoleVisibility.bind(this);
    this.getMacroFiles = this.projectManagement.getMacroFiles.bind(
      this.projectManagement
    );

    this.keyInterface = new KeYInterface(
      this.stompService,
      this.notificationSystem,
      this.setProvenObligations,
      () => this.state.proofsState,
      proofsState => this.setState({ proofsState }),
      obligationId =>
        this.setState({ obligationIdOfLastUpdatedProof: obligationId }),
      () => this.state.project.name + '/' + this.state.openedPath.join('/')
    );

    this.editor = React.createRef();
    this.console = React.createRef();

    // setup initial state
    this.state = {
      /**
       * The currently opened project. For example, it's displayed within
       * the Sidebar component.
       */
      project: {},

      // content of the current file. Displayed within the editor.
      text: '',

      // currently opened file in the editor
      openedPath: [],

      // type of the currently opened file in the editor
      filetype: '',

      // warnings, errors, etc. within the currently open file
      diagnostics: [],

      // indices of obligations, that have been proven
      provenObligations: [],

      // console visibilty
      consoleIsVisible: false,

      proofsState: ProofsState.create(),

      obligationIdOfLastUpdatedProof: undefined,
    };
  }

  /**
   * Set the currently open project to another project.
   * Passed down to the sub components, so that menu options etc. can change
   * the opened project.
   */
  showProject(project) {
    this.setState({
      project: project,
    });
  }

  /**
   * Set the content of the currently open file.
   * Passed down to the sub components, so that the editor can apply changes.
   */
  setText(text) {
    this.setState({
      text: text,
    });
  }

  setFileName(filename) {
    let path = this.state.openedPath;
    path[path.length - 1] = filename;
    this.setOpenedPath(path);
  }

  /**
   * Sets the path of the currently opened file, which is passed down to the components
   */
  setOpenedPath(path) {
    let filetype = '';
    console.log(path);
    if (path && path[path.length - 1]) {
      const filename = path[path.length - 1];
      filetype = filename.split('.')[filename.split('.').length - 1];
    }
    this.setState({
      openedPath: path,
      filetype: filetype,
    });
    if (this.collabController) {
      this.collabController.setFile(
        this.state.project.name,
        path.join('/'),
        this.state.text
      );
      this.keyInterface.setCurrentFile(this.state.project.name, path, false);
      this.consoleSyncController.openFile(this.state.project.name, path);
    }
    this.displayCloseButton = false;
  }

  /**
   * Sets warnings, errors etc, for the currently opened file.
   * Passed down to the sub components, so that linter methods can be applied.
   */
  setDiagnostics(diagnostics) {
    this.setState({
      diagnostics: diagnostics,
    });
  }

  /**
   * Set the results of proofs carried out by key
   * @param provenObligations - provenObligations
   */
  setProvenObligations(provenObligations) {
    this.setState({
      provenObligations: provenObligations,
    });
  }

  /**
   * Reset/remove a result of a proof carried out previously. Useful when a
   * proof should be carried out again
   * @param obligationIdx - the index of the obligation whose result should
   * be reset
   */
  resetObligation(obligationIdx) {
    const provenObligations = this.state.provenObligations.filter(
      provenObligationIdx => provenObligationIdx !== obligationIdx
    );

    this.setState({
      provenObligations,
    });
  }

  /**
   * Save an obligation result permanently on the server side
   * @param obligationResult - the result that should be saved
   */
  saveObligationResult(obligationResult) {
    this.keyInterface.saveObligationResult(
      this.state.project.name,
      this.state.openedPath.join('/'),
      obligationResult
    );
  }

  /**
   * Delete an obligation result permanently on the server side
   * @param obligationResult - the result that should be deleted
   */
  deleteObligationResult(obligationIdx, historyIdx) {
    this.keyInterface.deleteObligationResult(
      this.state.project.name,
      this.state.openedPath.join('/'),
      obligationIdx,
      historyIdx
    );
  }

  proveFile() {
    this.setState({
      provenObligations: [],
    });

    this.keyInterface.proveFile();
  }

  /**
   * This function inverts the visibilty of the
   * console compontent
   *
   */
  setConsoleVisibility(visible) {
    this.setState({
      consoleIsVisible: visible,
    });
  }

  /**
   * React lifecycle method: Called after this component has been initialized
   * and inserted into the DOM tree.
   */
  componentDidMount() {
    document.title = 'KollaborierbaR';

    this.collabController = new CollabController(
      this.stompService,
      this.editor.current,
      this.setText.bind(this)
    );

    let errorMessages = new ErrorMessages(this.notificationSystem);

    this.consoleSyncController = new ConsoleSyncController(
      this.stompService,
      this.console.current,
      errorMessages
    );

    this.setState({
      text: '',
      openedPath: [],
    });
    document.addEventListener('keydown', this.handleCtrlS.bind(this));
  }

  /**
   * Open a file and display its contents in the editor
   * @param path - the file path as a list of files, relative to the project
   * root folder
   */
  openFile(path) {
    // This string composition is necessary because path contains only the path within a project.
    ProjectManagement.openFile(
      this.state.project.name + '/' + path.join('/')
    ).then(response => {
      this.setState({
        text: response.fileText,
        provenObligations: [],
        proofsState: ProofsState.create(),
      });
      // TODO: Handle rename with collab controller
      this.setOpenedPath(path);
    });
  }

  /**
   * Display a sequent of a proof in the editor text field.
   * Also display a button to close the sequent and return to the file
   * @param formula - the sequent formula that should be displayed
   */
  displaySequent(formula) {
    this.collabController.disconnect();
    this.setState({
      text: formula,
      filetype: 'sequent',
      diagnostics: [],
    });
    this.displayCloseButton = true;
  }

  /**
   * Close a sequent and display the previous file. Also hide the sequent
   * close button
   */
  closeSequent() {
    this.openFile(this.state.openedPath);
    this.displayCloseButton = false;
  }

  /**
   * Eventhandler method for keyevent (CTRL + S).
   * On CTRL + S the opened file will be saved persistent on the server
   *
   */
  handleCtrlS(event) {
    if (event.keyCode === 83 && event.ctrlKey) {
      // Prevent default save file context menu
      event.preventDefault();

      this.saveFile();
    }
  }

  /**
   * This function instances updateFileContent to save files.
   * This method is then handed down to the react components, which
   * need to save the fileContent.(app knows who to instances
   * updateFileContent, the other react components dont)
   */
  saveFile() {
    if (this.state.filetype !== 'sequent') {
      return this.updateFileContent(this.state.openedPath, this.state.text);
    } else {
      return Promise.reject();
    }
  }

  /**
   * Creates the displayed HTML for this component.
   *
   * For now it will render a menu, a project overview (sidebar) and an
   * editor.
   */
  render() {
    return (
      <div>
        {/**
         * create the sub components mentioned above and pass them the
         * state variables and state manipulation functions they need
         * to operate.
         */}
        {/* Render the top component */}
        <Top
          getFilePath={this.projectManagement.getOpenedPath}
          setText={this.setText}
          text={this.state.text}
          onDeleteFile={() => this.deleteFile(this.state.openedPath)}
          onDeleteProject={this.deleteProject}
          onOpenProject={this.openProject}
          onCreateProject={this.createProject}
          onProveFile={this.proveFile}
          onUpdateFileName={() => {
            this.updateFileName(this.state.openedPath);
          }}
          onSelectMacro={this.keyInterface.setMacro}
          saveFile={this.saveFile}
          notificationSystem={this.notificationSystem}
          getMacroFiles={this.getMacroFiles}
          //TODO: onDeleteProject={this.deleteProject}
        />
        <div id="mainContainer">
          {/* Render the sidebar component */}
          <Sidebar
            project={this.state.project}
            proofsState={this.state.proofsState}
            obligationIdOfLastUpdatedProof={
              this.state.obligationIdOfLastUpdatedProof
            }
            openedPath={this.state.openedPath}
            //TODO: Code auslagern in die aufrufenden Funktionen
            onOpenFile={this.openFile}
            onDeleteFile={this.deleteFile}
            onCreateFile={this.createFile}
            onDeleteProject={this.deleteProject}
            onUpdateFileName={this.updateFileName}
            displayFormula={this.displaySequent}
            saveObligationResult={this.saveObligationResult}
            deleteObligationResult={this.deleteObligationResult}
          />
          <div className="rightSide">
            {// Only display the button if this variable is true
            this.displayCloseButton && (
              <Button
                color="danger"
                onClick={this.closeSequent}
                style={{
                  position: 'absolute',
                  zIndex: 10,
                  right: '10px',
                  top: '10px',
                  borderRadius: '100px',
                }}
              >
                <i className="fa fa-times" />
              </Button>
            )}
            {/* Render the editor component, if there is a project/file to display */}
            <Toggleable
              className="appMainContent"
              isVisible={
                this.state.project.name != null &&
                this.state.openedPath.length > 0
              }
            >
              <Editor
                saveFile={this.saveFile}
                setDiagnostics={this.setDiagnostics}
                diagnostics={this.state.diagnostics}
                provenObligations={this.state.provenObligations}
                resetObligation={this.resetObligation}
                setText={this.setText}
                text={this.state.text}
                filepath={this.state.openedPath}
                filetype={this.state.filetype}
                collabController={this.collabController}
                getObligations={this.keyInterface.getObligations}
                getContractsForMethod={this.keyInterface.getContractsForMethod}
                onProveObligations={this.keyInterface.proveObligations}
                ref={this.editor}
                consoleIsVisible={this.state.consoleIsVisible}
              />
              {/* Render the console component */}
              <Console
                ref={this.console}
                visible={this.state.consoleIsVisible}
                setVisibility={this.setConsoleVisibility}
              />
            </Toggleable>
            {/* render the welcome screen, if there is not a file to display yet */}
            <Toggleable className="appMainContent" isVisible={true}>
              <WelcomeScreen
                project={this.state.project}
                isVisible={
                  this.state.project.name == null ||
                  this.state.openedPath.length === 0
                }
              />
            </Toggleable>
          </div>
        </div>
        <ConfirmationModal ref={this.confirmationModal} />
        <NotificationSystem ref={this.notificationSystem} />
      </div>
    );
  }
}
