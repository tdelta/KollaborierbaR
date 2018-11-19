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

import 'brace/mode/java';
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
        lint('Test', this.editor.getValue())
            .then((diagnostics) => {
                this.props.setDiagnostics(diagnostics);
            });
    }

    setAnnotations(){
        this.editor.getSession().setAnnotations(
            this.props.diagnostics.map(toAnnotation));
    }

    componentDidMount(){
        this.editor = brace.edit('editor');
        this.timeTest = null;
        this.editor.setOptions({
            autoScrollEditorIntoView: true,
            copyWithEmptySelection: true,
            fontSize: 20,
            firstLineNumber: 1,
        });
        this.editor.getSession().setMode('ace/mode/java');
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
            text: 'public class Test {\r\n\tpublic static void main(String[] args){\r\n\t\tSystem.out.println("Hello World");\r\n\t\t\r\n\t\tswitch (2) {\r\n\t\t    case 1:\r\n\t\t        System.out.println("1");\r\n\t\t    case 2: //there be warnings, try linting!\r\n\t\t        System.out.println("2"); \r\n\t\t}\r\n\t}\r\n}'
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
