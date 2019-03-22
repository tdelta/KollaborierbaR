import React, { RefObject } from 'react';
import { Tooltip } from 'reactstrap';

export default class MarkerPopover extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.state = { isOpen: false };
  }

  public render() {
    return (
      <Tooltip
        placement="top"
        target={this.props.target}
        isOpen={this.state.isOpen}
      >
        {this.props.children}
      </Tooltip>
    );
  }

  public hide() {
    this.setState({ isOpen: false });
  }
}

interface Props {
  target: HTMLElement;
}

interface State {
  isOpen: boolean;
}
