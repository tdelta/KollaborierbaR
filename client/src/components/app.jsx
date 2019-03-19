import React from 'react';

import NotificationSystem from 'react-notification-system';

import Editor from './editor.tsx';
import Top from './top.tsx';
import Sidebar from './sidebar/sidebar.jsx';
import ConfirmationModal from './confirmation-modal.tsx';
import Console from './console/console.jsx';
import {Network} from '../network';

import ProofsState from '../key/ProofsState';

import ProjectManagement from '../projectmanagement.ts';

import CollabController from '../collaborative/CollabController.ts';

import Key from '../key/key';

import {Button} from 'reactstrap';

//import testSource from '../sample-text.js';

/**
 * Main component of KollaborierbaR. Renders all other components (Editor etc.)
 * while holding global state.

//import testSource from '../sample-text.js';

/**
 * Main component of KollaborierbaR. Renders all other components (Editor etc.)
 * while holding global state.
 */
export default class App extends React.Component {
    constructor(props){
        super(props);

        this.confirmationModal = React.createRef();
        this.notificationSystem = React.createRef();
        this.displayCloseButton = false;

        this.network = new Network({
          onConnect: () => console.log("Connected websocket.")
        });

        this.projectManagement = new ProjectManagement(
            this.network,
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
        this.deleteFile = (path) => this.projectManagement.deleteFile(this.state.openedPath,this.state.project.name, path);
        this.deleteProject = (path) => this.projectManagement.deleteProject(this.state.project.name, path);
        this.createFile = (path, type) => this.projectManagement.createFile(this.state.project.name, path, type);
        this.createProject = this.projectManagement.createProject.bind(this.projectManagement);
        this.openProject = this.projectManagement.openProject.bind(this.projectManagement);
        this.updateFileName = this.projectManagement.updateFileName.bind(this.projectManagement);
        this.updateFileContent = this.projectManagement.updateFileContent.bind(this.projectManagement);
        this.addNewConsoleMessage = this.addNewConsoleMessage.bind(this);
        this.invertConsoleVisibility = this.invertConsoleVisibility.bind(this);

        this.key = new Key(
          this.network,
          this.notificationSystem,
          this.setProvenObligations,
          () => this.state.proofsState,
          (proofsState) => this.setState({proofsState}),
          (obligationId) => this.setState({obligationIdOfLastUpdatedProof: obligationId}),
          () => this.state.project.name + '/' + this.state.openedPath.join('/'),
          this.addNewConsoleMessage
        );

        this.editor = React.createRef();

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

            // the console log
            consolelog: '',

            // console visibilty
            consoleIsVisible: false,

            proofsState: ProofsState.create(),

            obligationIdOfLastUpdatedProof: undefined
        };
    }

    /**
     * Set the currently open project to another project.
     * Passed down to the sub components, so that menu options etc. can change
     * the opened project.
     */
    showProject(project) {
        this.setState({
            'project': project,
        });
    }

    /**
     * Set the content of the currently open file.
     * Passed down to the sub components, so that the editor can apply changes.
     */
    setText(text){
        this.setState({
            text: text
        });
    }

    setFileName(filename){
        let path = this.state.openedPath;
        path[path.length - 1] = filename;
        this.setOpenedPath(path);
    }
    
    /**
     * Sets the path of the currently opened file, which is passed down to the components
     */
    setOpenedPath(path){
        let filetype = '';
        console.log(path);
        if(path && path[path.length-1]){
            const filename = path[path.length-1]
            filetype = filename.split('.')[filename.split('.').length-1];
        }  
        this.setState({
            openedPath: path,
            filetype: filetype
        });
        if(this.collabController){
            this.collabController.setFile(this.state.project.name,path.join('/'),this.state.text);
            this.key.setCurrentFile(this.state.project.name, path);
        }
        this.displayCloseButton=false;
    }

    /**
     * Sets warnings, errors etc, for the currently opened file.
     * Passed down to the sub components, so that linter methods can be applied.
     */
    setDiagnostics(diagnostics){
        this.setState({
            'diagnostics': diagnostics
        });
    }

    setProvenObligations(provenObligations) {
        this.setState({
          provenObligations: provenObligations
        });
    }

    resetObligation(obligationIdx) {
        const provenObligations = this.state.provenObligations
          .filter(provenObligationIdx => provenObligationIdx !== obligationIdx);

        this.setState({
          provenObligations
        });
    }

    saveObligationResult(obligationResult) {
      this.key.saveObligationResult(this.state.project.name, this.state.openedPath.join('/'), obligationResult);
    }

    deleteObligationResult(obligationIdx, historyIdx) {
      this.key.deleteObligationResult(this.state.project.name, this.state.openedPath.join('/'), obligationIdx, historyIdx);
    }

    proveFile() {
        this.setState({
          provenObligations: []
        });

        this.key.proveFile();
    }

    addNewConsoleMessage(message) {
        
        //Create time string
        let date = new Date();
        let h = date.getHours();
        let m = date.getMinutes();
        let s = date.getSeconds();

        let timeString = h + ":" + m + ":" + s;

        this.setState({
            consolelog: this.state.consolelog+ timeString + " " + message + "\n",
            consoleIsVisible: true
        });
    }

    invertConsoleVisibility(){
        this.setState({
            consoleIsVisible: ! this.state.consoleIsVisible
        });
    }

    /**
     * React lifecycle method: Called after this component has been initialized
     * and inserted into the DOM tree.
     */
    componentDidMount() {
        document.title = "KollaborierbaR";

        this.collabController = new CollabController(
            this.network,
            this.editor.current,
            this.setText.bind(this)
        );
        this.setState({
            text: '',
            openedPath: []
        });
        document.addEventListener('keydown', this.handleCtrlS.bind(this));
    }

    componentDidUpdate(prevProps, prevsState) {
    }

    openFile(path) {
        // This string composition is necessary because path contains only the path within a project.
        ProjectManagement.openFile(this.state.project.name + '/' + path.join('/'))
            .then((response) => {
                this.setState({
                    text: response.fileText,
                    provenObligations: [],
                    proofsState: ProofsState.create()
                });
                // TODO: Handle rename with collab controller
                this.setOpenedPath(path);
            });
    }

    displaySequent(formula){
      this.collabController.disconnect();
      this.setState({
        text: formula,
        filetype: 'sequent',
        diagnostics: []
      });
      this.displayCloseButton=true;
    }

    closeSequent(){
      this.openFile(this.state.openedPath);
      this.displayCloseButton=false;
    }


    /**
     * Eventhandler method for keyevent (CTRL + S).
     * On CTRL + S the opened file will be saved persistent on the server
     * 
     */
    handleCtrlS(event){
        if(event.keyCode === 83 && event.ctrlKey){
            // Prevent default save file context menu
            event.preventDefault();

            this.saveFile();
        }
    }

    saveFile() {
      if (this.state.filetype !== 'sequent') {
          return this.updateFileContent(this.state.openedPath, this.state.text);
      }

      else {
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
        return(
            <div>
                {/**
                  * create the sub components mentioned above and pass them the
                  * state variables and state manipulation functions they need
                  * to operate.
                  */}
                <Top
                    setText={this.setText}
                    text={this.state.text}
                    onDeleteFile={() => this.deleteFile(this.state.openedPath)}
                    onDeleteProject={this.deleteProject}
                    onOpenProject={this.openProject}
                    onCreateProject={this.createProject}
                    onProveFile={this.proveFile}
                    onUpdateFileName={() => {this.updateFileName(this.state.openedPath);}}
                    saveFile={this.saveFile}
                    notificationSystem={this.notificationSystem}
                    //TODO: onDeleteProject={this.deleteProject}
                />
                <div id="mainContainer">
                    <Sidebar
                        project={this.state.project}
                        proofsState={this.state.proofsState}
                        obligationIdOfLastUpdatedProof={this.state.obligationIdOfLastUpdatedProof}
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
                    <div class="rightSide">
                        {
                        // Only display the button if this variable is true
                        this.displayCloseButton &&
                        <Button 
                            color='danger'
                            onClick={this.closeSequent}
                            style={{
                                position:'absolute', 
                                zIndex:10, 
                                right:'10px', 
                                top:'10px', 
                                borderRadius:'100px'
                            }}>
                            <i class="fa fa-times"></i>
                        </Button>
                        }
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
                            getObligations={this.key.getObligations}
                            getContractsForMethod={this.key.getContractsForMethod}
                            onProveObligations={this.key.proveObligations}
                            ref={this.editor}
                            consoleIsVisible = {this.state.consoleIsVisible}
                        />
                        <Console
                            consolelog = {this.state.consolelog}
                            consoleIsVisible = {this.state.consoleIsVisible}
                            invertConsoleVisibility = {this.invertConsoleVisibility}
                        />
                    </div>
                </div>
                <ConfirmationModal ref={this.confirmationModal}/>
                <NotificationSystem ref={this.notificationSystem}/>
            </div>
        );
    }
}
