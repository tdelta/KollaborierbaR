import React from 'react';
import PropTypes from 'prop-types';
import { Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

class KeyModal extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            modal: false,
            proofLog: 'Proving proof obligations...'
        };
    }

    runProof() {
        this.props.runProof()
            .then((response) => { 
              this.setState({proofLog: response});
            });
    }

    closeProofModal(){
        this.state.proofLog = 'Proving proof obligations...'; 
    }

    render() {
        return (
            <div>
                <Modal isOpen={this.props.isOpen} toggle={this.props.toggle} onOpened={() => this.runProof()} onClosed={() => this.closeProofModal()}>
                    <ModalHeader toggle={this.toggle}>Results</ModalHeader>
                    <ModalBody>
                        {this.state.proofLog}
                    </ModalBody>
                    <ModalFooter>
                        <Button color="primary" onClick={this.props.toggle}>Ok</Button>{' '}
                    </ModalFooter>
                </Modal>
            </div>
        );
    }
}
KeyModal.propTypes = {
    runProof: PropTypes.func,
    isOpen: PropTypes.bool,
    toggle: PropTypes.func
};

export default KeyModal;
