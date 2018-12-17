import React from 'react';

import Editor from './editor.tsx';
import Top from './top.tsx';
import Sidebar from './sidebar/sidebar.jsx';
import ConfirmationModal from './confirmation-modal.tsx';

import openFile from '../openFile.js';

import {deleteFile, createFile, deleteProject} from './modal.js';

//import testSource from '../sample-text.js';

/**
 * Main component of KollaborierbaR. Renders all other components (Editor etc.)
 * while holding global state.
 */
export default class App extends React.Component {
    constructor(props){
        super(props);

        // all methods should always refer to this instance of App, when
        // using the `this` variable.
        this.setText = this.setText.bind(this);
        this.setFileName = this.setFileName.bind(this);
        this.setDiagnostics = this.setDiagnostics.bind(this);
        this.showProject = this.showProject.bind(this);

        this.confirmationModal = React.createRef();

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
            filename: 'Main.java'
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
                />
                <div id="mainContainer">
                    <Sidebar
                        project={this.state.project}
                        onOpenFile={(path) => {
                            // This string composition is necessary because path contains only the path within a project.
                            openFile('/' + this.state.project.name + '/' + path.join('/'))
                                .then((response) => {
                                    this.setText(response.fileText);
                                    this.setFileName(response.fileName);
                                });
                        }}
                        onDeleteFile={(path) => {
                            // This string composition is necessary because path contains only the path within a project.
                            deleteFile('/' + this.state.project.name + '/' + path.join('/'))
                                .then((response) => {
                                    // The response contains the new file structure, where the choosen file it deleted.
                                    this.showProject(response);
                                    // if the deleted file is the opened one, empty the editor
                                    if (path[path.length-1] === this.state.filename) {
                                        this.setText('');
                                        this.setFileName(undefined);
                                    }
                                });
                        }}
                        onCreateFile={(path) => {
                        
                            createFile('/' + this.state.project.name + '/' + path.join('/'))
                                .then((response) => {
                                    this.showProject(response);
                                });
                        }}
                        onDeleteProject={() => {
                            // Show a dialog to confirm the deletion of the project
                            this.confirmationModal.current.ask(
                                `Really delete project ${this.state.project.name}?`,
                                // Called when the dialog was confirmed
                                () => {
                                    deleteProject(
                                        this.state.project.name, // Project to delete, in this case always the project that was opened
                                        this.showProject, // Callback that renders the resulting project
                                        this.state.project.name // Currently opened project
                                    );
                                },
                                // Empty function called when the dialog was canceled
                                ()=>{});
                        }}
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
            </div>
        );
    }
}
