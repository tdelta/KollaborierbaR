import { UncontrolledTooltip } from 'reactstrap';
import React from 'react';
import './animals.css';

export default class UserIndicator extends React.Component<Props, {}> {
  constructor(props: Props) {
    super(props);
  }

  public render() {
    return (
      <>
        <span className="login-text" id={this.props.name}>
          <div
            style={{ backgroundColor: this.props.color }}
            className={'circle'}
          >
            {this.props.name.charAt(0)}
          </div>
        </span>
        <UncontrolledTooltip
          delay={{ show: 0, hide: 0 }}
          placement="bottom"
          target={this.props.name}
        >
          {this.props.name}
        </UncontrolledTooltip>
      </>
    );
  }

  /*#4CAF50
   *#FF5722
   *#448AFF
   *#00BCD4
   *#D32F2F
   *#FF4081
   *#9E9E9E
   *#FFEB3B
   *#009688
   *#7C4DFF
   */
}

interface Props {
  name: string;
  color: string;
}
