import { UncontrolledTooltip } from 'reactstrap';
import React from 'react';
import './animals.css';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesomeIcon from 'react-fontawesome';

export default class UserIndicator extends React.Component<Props, {}> {
  constructor(props: Props) {
    super(props);
  }

  /*
   * Gives the color coresponding with the given number.
   * This corresponds to the colors specified in {@link src/collaborative/marker-colors.css}
   * that are displayed in the editor.
   * @param number given
   * @returns string contain color in hex
   */
  public getColor(crdtId: number): string {
    const colors = [
      '#4CAF50',
      '#009688',
      '#9E9E9E',
      '#00BCD4',
      '#448AFF',
      '#D32F2F',
      '#FF4081',
      '#FF5722',
      '#FFEB3B',
      '#7C4DFF',
    ];
    return colors[crdtId % 10] || '#C70039';
  }

  /*
   * Capitalizes the first char of a string and returns the new string
   * @param string given
   * @returns converted string
   */
  public capitalize(text: string): string {
    return text.charAt(0).toUpperCase() + text.slice(1);
  }

  /**
   * React callback that creates the html elements
   */
  public render() {
    return (
      <>
        {/** Render a circle with the color corresponding to the given crdtId */}
        <span className="login-text" id={`user-circle-${this.props.uid}`}>
          <div
            style={{
              backgroundColor: this.getColor(this.props.crdtId),
              color: '#343a40',
            }}
            className={'circle'}
          >
            {/** Render an icon corresponding the given animal name */}
            <FontAwesomeIcon
              name={
                this.props.lastName === 'kiwi'
                  ? 'kiwi-bird'
                  : this.props.lastName
              }
              style={{ margin: 'auto' }}
            />
          </div>
        </span>
        {/** Render a tooltip that displays the given name, when the user hovers over the circle */}
        <UncontrolledTooltip
          delay={{ show: 0, hide: 0 }}
          placement="bottom"
          target={`user-circle-${this.props.uid}`}
        >
          {`${this.props.firstName} ${this.capitalize(this.props.lastName)}`}
        </UncontrolledTooltip>
      </>
    );
  }
}

// defining the structure of this react components properties
interface Props {
  uid: number;
  firstName: string;
  lastName: string;
  crdtId: number;
}
