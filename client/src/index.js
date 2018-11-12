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
        this.downloadSelector = React.createRef();
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
            <DropdownItem onClick={(e)=> this.downloadSelector.current.click()}>
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
        
        <a href={'data:text/plain;charset=utf-8,'+ encodeURIComponent(this.props.text)} download='test.txt'>
            <input type="button" ref={this.downloadSelector} style={{display: "none"}}/>
        </a>

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
        let aceDiagnostics = this.props.diagnostics.map(toAnnotation);
        this.editor.getSession().setAnnotations(aceDiagnostics);

        for (var i = 0; i < this.markers.length; i++) {
            this.editor.session.removeMarker(this.markers[i]);
        }
        this.markers = [];

        for (var i = 0; i < aceDiagnostics.length; i++) {
            let startRow = aceDiagnostics[i]["startRow"];
            let startCol = aceDiagnostics[i]["startCol"];
            let endRow = aceDiagnostics[i]["endRow"];
            let endCol = aceDiagnostics[i]["endCol"];
            var Range = brace.acequire('ace/range').Range;
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
