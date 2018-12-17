import React from 'react';
import { Button, Modal, ModalHeader, ModalBody, ModalFooter } from 'reactstrap';

interface State {
  isOpen: boolean;
  question: string;
}

/**
 * Modal to be used to ask the user for confirmation on any action.
 *
 * See `ask` method for usage.
 *
 * TODO: Better documentation
 */
export default class ConfirmationModal extends React.Component<{}, State> {
    private onConfirmed: () => void = () => undefined;
    private onCancelled: () => void = () => undefined;

    constructor(props: object) {
        super(props);

        this.state = {
          isOpen: false,
          question: ""
        };

        this.ask = this.ask.bind(this);
        this.confirm = this.confirm.bind(this);
        this.cancel = this.cancel.bind(this);
    }

    private confirm(): void {
      this.setState({
        isOpen: false
      });

      this.onConfirmed();
    }

    private cancel(): void {
      this.setState({
        isOpen: false
      });

      this.onCancelled();
    }

    /**
     * Call this method to trigger the confirmation dialog.
     *
     * @param question Text which informs the user, which question or action shall be confirmed.
     * @param onConfirmed Will be called, if the user selects the `confirm` button.
     * @param onCancelled Will be called, if the user selects the `cancel` button.
     */
    public ask(
      question: string,
      onConfirmed: () => void = () => undefined,
      onCancelled: () => void = () => undefined
    ) {
      this.onConfirmed = onConfirmed;
      this.onCancelled = onCancelled;

      this.setState({
        isOpen: true,
        question: question
      });
    }

    public render() {
        return (
          <>
            <Modal isOpen={this.state.isOpen}>
                <ModalHeader>Please confirm</ModalHeader>

                <ModalBody style={{'maxHeight': 'calc(100vh - 210px)', 'overflowY': 'auto'}}>
                    {this.state.question}
                </ModalBody>

                <ModalFooter>
                    <Button color="danger" onClick={this.confirm}>Confirm</Button>
                    <Button color="secondary" onClick={this.cancel}>Cancel</Button>
                </ModalFooter>
            </Modal>
          </>
        );
    }
}
