import { UncontrolledTooltip } from 'reactstrap';
import React from 'react';
import './animals.css';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesomeIcon from 'react-fontawesome';

export default class UserIndicator extends React.Component<Props, {}> {

  constructor(props: Props) {
    super(props);
      }

  public getColor(crdtId: number): string{
  const colors = ["#4CAF50","#FF5722","#448AFF",
   "#00BCD4",
   "#D32F2F",
   "#FF4081",
   "#9E9E9E",
   "#FFEB3B",
   "#009688",
   "#7C4DFF"];
    return colors[crdtId%10];
  }

  public render() {
    return (
      <>
        <span className="login-text" id={this.props.firstName}>
          <div
            style={{ backgroundColor: this.getColor(this.props.crdtId), color: '#343a40' }}
            className={'circle'}
          >
                    <FontAwesomeIcon
                        name={this.props.lastName}
                        style={{ margin: 'auto' }}
                    />
          </div>
        </span>
        <UncontrolledTooltip
          delay={{ show: 0, hide: 0 }}
          placement="bottom"
          target={this.props.firstName}
        >
          {this.props.firstName}
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
  firstName: string;
  lastName: string;
  crdtId: number;
}
