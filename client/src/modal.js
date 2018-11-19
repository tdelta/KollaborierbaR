/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import { ListGroup, ListGroupItem, Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

class ModalSelect extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      modal: true
    };
    this.toggle = this.toggle.bind(this);
  }

    myClick() {
        alert("Hello World!");
    }
    myAss() {
        var rows = [];
        for (var i = 0; i < 5; i++) {
            // note: we add a key prop here to allow react to uniquely identify each
            // element in this array. see: https://reactjs.org/docs/lists-and-keys.html
          rows.push(<ListGroupItem key={i} onClick={() => this.myClick()} action>Project {i}</ListGroupItem>)
        }
        return <tbody>{rows}</tbody>;
    }
  toggle() {
    this.setState({
      modal: !this.state.modal
    });
  }
    componentWillReceiveProps(nextProps){
        this.setState({modal: nextProps.isOpen});
    }
  render() {
    return (
      <div>
        <Modal isOpen={this.state.modal} toggle={this.toggle} className={this.props.className}>
          <ModalHeader toggle={this.toggle}>Select Project</ModalHeader>
          <ModalBody>
        <ListGroup>
            {this.myAss()}
        </ListGroup>
          </ModalBody>
          <ModalFooter>
            <Button color="primary" onClick={this.toggle}>Select</Button>{' '}
            <Button color="secondary" onClick={this.toggle}>Cancel</Button>
          </ModalFooter>
        </Modal>
      </div>
    );
  }
}

export default ModalSelect;
