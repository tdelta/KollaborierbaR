import React from 'react';
import ReactDOM from 'react-dom';
import './index.css';

import brace from 'brace';
import AceEditor from 'react-ace';

import Bootstrap from 'bootstrap/dist/css/bootstrap.css';

import {
    Collapse,
    Navbar,
    NavbarToggler,
    NavbarBrand,
    Nav,
    NavItem,
    NavLink,
    Button,
    UncontrolledDropdown,
    DropdownToggle,
    DropdownMenu,
    DropdownItem } from 'reactstrap';

import lint from './linting.js';
import toAnnotation from './diagnostics.js';

import 'brace/mode/java';
import 'brace/theme/monokai';

class Top extends React.Component {
    constructor(props) {
        super(props);
        this.fileSelector = React.createRef();
        this.onFileChosen = this.onFileChosen.bind(this);
        this.onFileLoaded = this.onFileLoaded.bind(this);
        this.toggle = this.toggle.bind(this);
        this.state = {
            isOpen: false
        };
    }
    toggle() {
        this.setState({
            isOpen: !this.state.isOpen
        });
    }
    onFileChosen(event){
        this.fileReader = new FileReader();
        this.fileReader.onloadend = this.onFileLoaded;
        this.fileReader.readAsText(event.target.files[0]);
    }
    onFileLoaded(e){
        this.props.setText(this.fileReader.result);
    }
    render() {
    return(
        <div>
        <Navbar color="dark" dark expand="md">
        <NavbarBrand href="/">KollaborierbaR</NavbarBrand>
        <Collapse isOpen={this.state.isOpen} navbar>
        <Nav className="ml-auto" navbar>
        <UncontrolledDropdown nav inNavbar>
            <DropdownToggle nav caret>
            File
            </DropdownToggle>
            <DropdownMenu right>
            <DropdownItem>
            Save
            </DropdownItem>
            <DropdownItem onClick={(e)=>this.fileSelector.current.click()}>
            Load
            </DropdownItem>
            </DropdownMenu>
        </UncontrolledDropdown>
        </Nav>
        </Collapse>
        </Navbar>
        <input type="file" id="file" ref={this.fileSelector} style={{display: "none"}} onChange={this.onFileChosen}/>
        </div>
        );
    }
}

class Editor extends React.Component {
    callLinter(){
        lint("Test", this.editor.getValue())
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
        this.editor.on("change", (e) => {
            this.props.setText(this.editor.getValue());
        });
        this.editor.on("change", (e) => {
            clearTimeout(this.timeTest)
            this.timeTest = setTimeout(() => {this.callLinter()}, 1000)
        });
    }    
    componentDidUpdate(){
        // Wird aufgerufen, wenn React eine property, z.B. text oder diagnostics verändert
        this.setAnnotations();
        if(this.props.text!=this.editor.getValue()){
            this.editor.setValue(this.props.text,-1);
        }
    }
    render() {
    return (
    <div id="editor">
    </div>
    );
    }
}

class App extends React.Component {
    constructor(props){
        super(props);
        this.setText = this.setText.bind(this);
        this.setDiagnostics = this.setDiagnostics.bind(this);
        this.state = {
            text : '',
            diagnostics: []
        };
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
            text: 'public class Test {\r\n\tpublic static void main(String[] args){\r\n\t\tSystem.out.println(\"Hello World\");\r\n\t\t\r\n\t\tswitch (2) {\r\n\t\t    case 1:\r\n\t\t        System.out.println(\"1\");\r\n\t\t    case 2: //there be warnings, try linting!\r\n\t\t        System.out.println(\"2\"); \r\n\t\t}\r\n\t}\r\n}'
        });
    }
    render() {
    return(
    <div>
        <Top setText={this.setText} text={this.state.text}/>
        <Editor setDiagnostics={this.setDiagnostics} diagnostics={this.state.diagnostics} setText={this.setText} text={this.state.text}/>
    </div>
    );
    }
}

ReactDOM.render(
    <App />,
    document.getElementById('root')
);
