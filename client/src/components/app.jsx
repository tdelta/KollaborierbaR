import React from 'react';

import Editor from './editor.tsx';
import Top from './top.tsx';
import Sidebar from './sidebar/sidebar.jsx';

import openFile from '../openFile.js';

import CollabController from '../collaborative/CollabController';
import Network from '../collaborative/Network';

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

            filename: undefined,

            // warnings, errors, etc. within the currently open file
            diagnostics: []
        };

        this.network = new Network();
        this.network.openProject('test');
    }

    /**
     * Set the currently open project to another project.
     * Passed down to the sub components, so that menu options etc. can change
     * the opened project.
     */
    showProject(project) {
        this.setState({
            'project': project
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
        this.collabController.setFile(this.state.project+'/'+filename);
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
        this.collabController = new CollabController(
            new Network(),
            this.editor.current,
            this.setText.bind(this)
        );

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
                    />
                    <Editor
                        setDiagnostics={this.setDiagnostics}
                        diagnostics={this.state.diagnostics}
                        setText={this.setText}
                        text={this.state.text}
                        filename={this.state.filename}
                        collabController={this.collabController}
                        ref={this.editor}
                    />
                </div>
            </div>
        );
    }
}
