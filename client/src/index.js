import React from 'react';
import ReactDOM from 'react-dom';
import './index.css';

import brace from 'brace';

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

import lint from './linting.js'

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
    <NavItem>
      <Button color="info" onClick={()=>{
        lint("Test", this.props.text)
          .then((diagnostics) => {alert(JSON.stringify(diagnostics));});
      }}>lint</Button>{' '}
    </NavItem>
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
	constructor(props){
		super(props);
		this.state = {
			editor: null
		};
	}
	componentDidMount(){
		var editor = brace.edit("editor");
		editor.setOptions({
			autoScrollEditorIntoView: true,
			copyWithEmptySelection: true,
			fontSize: 20,
			firstLineNumber: 1,
		});
		editor.setValue(this.props.text,-1);
    editor.on("change", (e) => {
      this.props.setText(editor.getValue());
    });
		this.setState({
			editor:editor
		});
	}	
	componentDidUpdate(){
		// Wird aufgerufen, wenn React eine neue text property an die Komponente weitergibt
    // Nur aktualisieren, wenn unterschiedlich, um loop zu vermeiden
    if (this.state.editor.getValue() !== this.props.text) {
      this.state.editor.setValue(this.props.text,-1);
    }
	}
	render() {
	return (
	<div id = "editor">
	</div>
	);
	}
}

class App extends React.Component {
	constructor(props){
		super(props);
		this.setText = this.setText.bind(this);
		this.state = {
			text : 'public class Test {\n\tpublic static void main(String[] args){\n\t\tSystem.out.println("Hello World");\n\t}\n}'
		};
	}
	setText(text){
		this.setState({
			text:text
		});
	}
	render() {
	return(
	<div>
		<Top setText={this.setText} text={this.state.text}/>
		<Editor setText={this.setText} text={this.state.text}/>
	</div>
	);
	}
}

ReactDOM.render(
	<App />,
	document.getElementById('root')
);
