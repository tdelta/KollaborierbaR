import React from 'react';
import ReactDOM from 'react-dom';
import PropTypes from 'prop-types';
import './index.css';
import './sidebar.css';

import 'bootstrap/dist/css/bootstrap.css';
import brace from 'brace'; 
import {
    Navbar,
    NavbarBrand,
    Nav,
    UncontrolledDropdown,
    DropdownToggle,
    DropdownMenu,
    DropdownItem } from 'reactstrap';

import lint from './linting.js';
import toAnnotation from './diagnostics.js';
import ModalSelect from './modal.js';

import Sidebar from './sidebar.jsx';

import './highlighting/jml.js';
import 'brace/theme/monokai';

class Top extends React.Component {
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
                                        Load Project
                                        </DropdownItem>
                                        <DropdownItem onClick={() => this.fileSelector.current.click()}>
                                        Create Project
                                        </DropdownItem>
                                    </DropdownMenu>
                            </UncontrolledDropdown>
            <ModalSelect isOpen={this.state.showModal} toggle={this.toggleModal} setStructure={this.props.showProject} />
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
    text: PropTypes.String,
};

class Editor extends React.Component {
    callLinter(){
        lint('LimitedIntegerSet', this.editor.getValue())
            .then((diagnostics) => {
                this.props.setDiagnostics(diagnostics);
            });
    }

    // Function that sets and updates the annotations and markers
    setAnnotations(){

        // Transforms and sets the existing diagnostics to a format, which is compatible to Ace
        let aceDiagnostics = this.props.diagnostics.map(toAnnotation);
        this.editor.getSession().setAnnotations(aceDiagnostics);

        // Removes existing marker in the editor
        for (var i = 0; i < this.markers.length; i++) {
            this.editor.session.removeMarker(this.markers[i]);
        }

        this.markers = [];

        // Processs each element of array of aceDiagonistics
        for (var i = 0; i < aceDiagnostics.length; i++) {
            let startRow = aceDiagnostics[i]["startRow"];
            let startCol = aceDiagnostics[i]["startCol"];
            let endRow = aceDiagnostics[i]["endRow"];
            let endCol = aceDiagnostics[i]["endCol"];

            // Imports Range object
            var Range = brace.acequire('ace/range').Range;

            //Creates marker depending on the error type
            if (aceDiagnostics[i]["type"] == "error")
                this.markers.push(this.editor.session.addMarker(new Range(startRow, startCol, endRow, endCol), "errorMarker", "text"));
            else
                this.markers.push(this.editor.session.addMarker(new Range(startRow, startCol, endRow, endCol), "warningMarker", "text"));
        }


    }

    componentDidMount(){
        this.editor = brace.edit('editor');
        this.markers = [];
        this.timeTest = null;
        this.editor.setOptions({
            autoScrollEditorIntoView: true,
            copyWithEmptySelection: true,
            fontSize: 20,
            firstLineNumber: 1,
        });
        this.editor.getSession().setMode('ace/mode/jml');
        this.editor.setTheme('ace/theme/monokai');

        // editor event handlers
        this.editor.on('change', () => {
            this.props.setText(this.editor.getValue());
        });

        this.editor.on('change', () => {
            clearTimeout(this.timeTest);
            this.timeTest = setTimeout(() => {this.callLinter();}, 1000);
        });
    }    
    componentDidUpdate(){
        // Wird aufgerufen, wenn React eine property, z.B. text oder diagnostics verändert
        this.setAnnotations();

        if(this.props.text !== this.editor.getValue()){
            this.editor.setValue(this.props.text,-1);
        }
    }
    render() {
        const testProject = {
            'name': 'MyProject',
            'contents': [
                {
                    'name': 'src',
                    'type': 'folder',
                    'contents': [
                        {
                            'name': 'java',
                            'type': 'folder',
                            'contents': [
                                {
                                    'name': 'main',
                                    'type': 'folder',
                                    'contents': [
                                        {
                                            'name': 'Main.java',
                                            'type': 'file'
                                        },
                                        {
                                            'name': 'Test.java',
                                            'type': 'file'
                                        }
                                    ]
                                }
                            ]
                        },
                    ]
                },
                {
                    'name': 'README.md',
                    'type': 'file'
                }
            ]
        };

        return (
            <div id="mainContainer">
                <Sidebar
                    project={this.props.project}
                    onOpenFile={(path) => alert(path.join('/'))}
                >
                    <div id="editor">
                    </div>
                </Sidebar>
            </div>
        );
    }
}

Editor.propTypes = {
    setText: PropTypes.func.isRequired,
    setDiagnostics: PropTypes.func.isRequired,
    diagnostics: PropTypes.array,
    text: PropTypes.String,
};

class App extends React.Component {
    constructor(props){
        super(props);
        this.setText = this.setText.bind(this);
        this.setDiagnostics = this.setDiagnostics.bind(this);
        this.showProject = this.showProject.bind(this);
        this.state = {
            project: {},
            text : '',
            diagnostics: []
        };
    }
    showProject(project) {
        console.log(project);
        this.setState({
            'project': project
        });
    }
    setText(text){
        this.setState({
            text: text
        });
    }
    setDiagnostics(diagnostics){
        this.setState({
            'diagnostics': diagnostics
        });
    }
    componentDidMount() {
        this.setState({
            // source code from a FMISE exercise, to test JML highlighting
            text: 'public class LimitedIntegerSet {\r\n\r\n\t//@ public invariant (\\forall int i,j; i>=0 && i<j && j<size; arr[i] != arr[j]);\r\n\tprivate /*@ spec_public @*/ int[] arr;\r\n\t\r\n\t//@ public invariant size >= 0 && size <= arr.length;\r\n\tprivate /*@ spec_public @*/ int size;\r\n\r\n\r\n\tpublic LimitedIntegerSet(int limit) {\r\n\t\tthis.arr = new int[limit];\r\n\t}\r\n\r\n\r\n\t/*@ public normal_behavior\r\n      @ ensures \\result == (\\exists int i;\r\n      @                             0 <= i && i < size;\r\n      @                             arr[i] == elem);\r\n      @*/\r\n\tpublic /*@ pure @*/ boolean contains(int elem) {/*...*/ throw new RuntimeException(\"Not yet implemented\");}\r\n\r\n\r\n\r\n\t/*@ public normal_behavior\r\n\t  @ requires contains(elem);\r\n      @ assignable size, arr[*];  // allows arbitrary reordering of the array elements\r\n      @ ensures !contains(elem); \r\n      @ ensures (\\forall int e;\r\n      @                  e != elem;\r\n      @                  contains(e) <==> \\old(contains(e)));\r\n      @ ensures size == \\old(size) - 1;\r\n      @\r\n      @ also\r\n      @ \r\n      @ public normal_behavior\r\n      @ requires !contains(elem);\r\n      @ assignable \\nothing;\r\n      @*/\r\n\tpublic void remove(int elem) {/*...*/}\r\n\r\n\r\n\t// we specify that the array is sorted afterwards and that the set has not changed; the latter works in this case and is easier \r\n\t// than if we would have to try to formalize permutation\r\n\t/*@ public normal_behavior\r\n\t  @ assignable a[0..size - 1];\r\n      @ ensures\r\n      @   (\\forall int i, j; i>=0 && i<j && j<size; arr[i]<arr[j]);\r\n      @ ensures (\\forall int e;  \r\n      @                  contains(e) <==> \\old(contains(e)));\r\n      @*/\r\n\tpublic void sort() { /* ... */ }\r\n\r\n\t\r\n\t/*@ public normal_behavior\r\n\t  @ requires size > 0;\r\n      @ assignable \\nothing;\r\n      @ ensures ( \\forall int i;\r\n      @                  i>=0 && i<size;\r\n      @                  \\result >= a[i] );\r\n      @ ensures ( \\exists int i;\r\n      @                  i>=0 && i<size;\r\n      @                  \\result == a[i] );\r\n      @\r\n      @ also\r\n      @ \r\n      @ public exceptional_behavior\r\n      @ requires size == 0;\r\n      @ assignable \\nothing;\r\n      @ signals  (RuntimeException) true;\r\n      @*/\r\n\tpublic int max() {\r\n\t\t// ...\r\n\t\tthrow new RuntimeException(\"Not yet implemented.\");\r\n\t}\r\n\t\r\n\r\n\r\n}\r\n'
        });
    }
    render() {
        return(
            <div>
                <Top showProject={this.showProject} setText={this.setText} text={this.state.text}/>
                <Editor project={this.state.project} setDiagnostics={this.setDiagnostics} diagnostics={this.state.diagnostics} setText={this.setText} text={this.state.text}/>
            </div>
        );
    }
}

ReactDOM.render(
    <App />,
    document.getElementById('root')
);
