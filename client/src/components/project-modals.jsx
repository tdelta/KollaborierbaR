/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import {
  ListGroup,
  ListGroupItem,
  Button,
  Modal,
  ModalHeader,
  ModalBody,
  ModalFooter,
} from 'reactstrap';
import ProjectManagement from '../projectmanagement.ts';

/*
 * open project dialog window, that shows a list with available projects
 */
class ModalSelect extends React.Component {
  constructor(props) {
    super(props);
    this.select = this.select.bind(this);
    this.projectAction = this.projectAction.bind(this);
    this.listProjects = this.listProjects.bind(this);
    this.state = {
      projects: [],
      selected: {
        id: -1,
        name: '',
      },
    };
  }

  /*
   * update the state with the selected project
   */
  select(name, id) {
    this.setState({
      selected: {
        id: id,
        name: name,
      },
    });
  }

  /*
   * performs the esired operation for the selected project when the select button is pressed
   * through the setStructure props method the structure starts its long journey to the sidebar
   */
  projectAction(name) {
    if (!name) {
      name = this.state.selected.name;
    }
    if (name) {
      this.props.projectOperation(this.state.selected.name);
      this.props.toggle();
    }
  }

  /*
   * generates  JSX items for each project name
   */
  listProjects() {
    //sort projects list
    this.state.projects.sort(function(a, b) {
      if (a.toLowerCase() < b.toLowerCase()) {
        return -1;
      }
      if (a.toLowerCase() > b.toLowerCase()) {
        return 1;
      }
      return 0;
    });
    // check, whether there are any projects in list
    if (this.state.projects && this.state.projects.length > 0) {
      return (
        <ListGroup>
          {// the id is an enumeration for the projects and used to check with project entry is active
          this.state.projects.map((name, id) => (
            <ListGroupItem
              key={id}
              onClick={() => {
                this.select(name, id);
              }}
              onDoubleClick={() => this.projectAction(name)}
              active={this.state.selected.id === id}
            >
              {name === '' ? 'None' : name}
            </ListGroupItem>
          ))}
        </ListGroup>
      );
    }

    // if there arent any, inform the user about it
    else {
      return <>{this.props.none}</>;
    }
  }

  render() {
    return (
      <div>
        {/*
         * onOpened: reload the project list
         * onClosed: when the modal is closed set the selected state to an invalid index, so that on a reopen no projects are highlighted
         */}
        <Modal
          isOpen={this.props.isOpen}
          toggle={this.props.toggle}
          onOpened={this.props.onOpened.bind(this)}
          onClosed={() => this.select('', -1)}
          className={this.props.className}
        >
          <ModalHeader toggle={this.props.toggle}>
            {this.props.title}
          </ModalHeader>
          {/* the style enables a scrollbar, when the project names don't fit on the screen (100vh) with a 210 pixels margin */}
          <ModalBody
            style={{ maxHeight: 'calc(100vh - 210px)', overflowY: 'auto' }}
          >
            {/* generate the listed project names dynamically */}
            {this.listProjects()}
          </ModalBody>
          <ModalFooter>
            {/* projectAction is a prop and defines what to do with a project (e.g. deletion) */}
            <Button color="primary" onClick={this.projectAction}>
              Select
            </Button>
            <Button color="secondary" onClick={this.props.toggle}>
              Cancel
            </Button>
          </ModalFooter>
        </Modal>
      </div>
    );
  }
}

/*
 * loads the project list, called whenever a project modal is opened
 */
const loadProjectNames = function() {
  ProjectManagement.getProjects().then(projects => {
    this.setState({ projects: projects });
  });
};

const loadMacroFiles = function() {
  let options = this.props.loadFunction();
  if (options.length > 0) {
    options.push('');
  }
  this.setState({
    projects: options,
  });
};

/*
 * No inheritance from ModalSelect because it is considered bad practice in React.
 * See https://reactjs.org/docs/composition-vs-inheritance.html
 */
function OpenModal(props) {
  return (
    <ModalSelect
      {...props}
      title="Select Project To Open"
      none="There are no projects on the server"
      onOpened={loadProjectNames}
    />
  );
}

function DeleteModal(props) {
  return (
    <ModalSelect
      {...props}
      title="Select Project To Delete"
      none="There are no projects on the server"
      onOpened={loadProjectNames}
    />
  );
}

function MacroModal(props) {
  return (
    <ModalSelect
      {...props}
      title="Select Script For Proofs"
      none="Create a .script file in your project to use macros"
      onOpened={loadMacroFiles}
    />
  );
}

export { OpenModal, DeleteModal, MacroModal };
