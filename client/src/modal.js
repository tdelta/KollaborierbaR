/* eslint react/no-multi-comp: 0, react/prop-types: 0 */

import React from 'react';
import { ListGroup, ListGroupItem, Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

class ModalSelect extends React.Component {

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
  render() {
    return (
      <div>
        <Modal isOpen={this.props.isOpen} toggle={this.props.toggle} className={this.props.className}>
          <ModalHeader toggle={this.props.toggle}>Select Project</ModalHeader>
          <ModalBody>
        <ListGroup>
            {this.myAss()}
        </ListGroup>
          </ModalBody>
          <ModalFooter>
            <Button color="primary" onClick={this.props.toggle}>Select</Button>{' '}
            <Button color="secondary" onClick={this.props.toggle}>Cancel</Button>
          </ModalFooter>
        </Modal>
      </div>
    );
  }
}

export default ModalSelect;
