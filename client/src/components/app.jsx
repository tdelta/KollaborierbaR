import React from 'react';

import NotificationSystem from 'react-notification-system';

import Editor from './editor.tsx';
import Top from './top.tsx';
import Sidebar from './sidebar/sidebar.jsx';
import ConfirmationModal from './confirmation-modal.tsx';

import ProjectManagement from '../projectmanagement.ts';

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

        this.projectManagement = new ProjectManagement(
            this.showProject.bind(this),
            () => this.state.project,
            this.setText.bind(this),
            this.setFileName.bind(this),
            () => this.state.openedPath,
            this.confirmationModal,
            this.notificationSystem,
            this.openFile.bind(this)
        );

        // all methods should always refer to this instance of App, when
        // using the `this` variable.
        this.setText = this.setText.bind(this);
        this.setFileName = this.setFileName.bind(this);
        this.setDiagnostics = this.setDiagnostics.bind(this);
        this.showProject = this.showProject.bind(this);
        this.openFile = this.openFile.bind(this);
        this.deleteFile = (path) => this.projectManagement.deleteFile(this.state.filename, this.state.project.name, path);
        this.deleteProject = (path) => this.projectManagement.deleteProject(this.state.project.name, path);
        this.createFile = (path, type) => this.projectManagement.createFile(this.state.project.name, path, type);
        this.createProject = this.projectManagement.createProject.bind(this.projectManagement);
        this.openProject = this.projectManagement.openProject.bind(this.projectManagement);

        // setup initial state
        this.state = {
            /**
             * The currently opened project. For example, it's displayed within
             * the Sidebar component.
             */
            project: {}, 

            // content of the current file. Displayed within the editor.
            text: '',

            filename: undefined,

            openedPath: [],

            // warnings, errors, etc. within the currently open file
            diagnostics: []
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

    /**
     * Set the file name of the currently open file.
     * Passed down to the sub components, since linters / compilers may need it.
     */
    setFileName(filename){
        this.setState({
            filename: filename
        });
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

    /**
     * React lifecycle method: Called after this component has been initialized
     * and inserted into the DOM tree.
     */
    componentDidMount() {
        this.setState({
            text: '', // load some sample text for testing
            filename: 'Main.java',
            openedPath: ['Main.java'] // TODO: replace filename with this
        });

        this.notificationSystem.current.addNotification({
            message: 'Notification message',
            level: 'success',
            position: 'bc'
        });
    }

    openFile(path) {
        // This string composition is necessary because path contains only the path within a project.
        ProjectManagement.openFile('/' + this.state.project.name + '/' + path.join('/'))
            .then((response) => {
                this.setState({
                    text: response.fileText,
                    filename: response.fileName,
                    openedPath: path
                });
            });
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
                    showProject={this.showProject}
                    setText={this.setText}
                    text={this.state.text}
                    onDeleteFile={() => this.deleteFile(this.state.openedPath)}
                    onDeleteProject={this.deleteProject}
                    onOpenProject={this.openProject}
                    onCreateProject={this.createProject}
                    //TODO: onDeleteProject={this.deleteProject}
                />
                <div id="mainContainer">
                    <Sidebar
                        project={this.state.project}
                        openedPath={this.state.openedPath}
                        //TODO: Code auslagern in die aufrufenden Funktionen
                        onOpenFile={this.openFile}
                        onDeleteFile={this.deleteFile}
                        onCreateFile={this.createFile}
                        onDeleteProject={this.deleteProject}
                    />
                    <Editor
                        setDiagnostics={this.setDiagnostics}
                        diagnostics={this.state.diagnostics}
                        setText={this.setText}
                        text={this.state.text}
                        filename={this.state.filename}
                    />
                </div>
                <ConfirmationModal ref={this.confirmationModal}/>
                <NotificationSystem ref={this.notificationSystem}/>
            </div>
        );
    }
}
