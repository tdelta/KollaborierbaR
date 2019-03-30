import React, { RefObject } from 'react';
import FontAwesome from 'react-fontawesome';
import '@fortawesome/fontawesome-free/css/all.min.css';
import './console.css';
import PropTypes from 'prop-types';
import {
  ConsoleEventObserver,
  ConsoleEvent,
} from '../../collaborative/ConsoleSyncController';

/**
 * This renders the console of KollaborierbaR. The
 * console is displayed depending on the consoleIsVisible
 * property handed down from app.jsx.
 */
export default class Console extends React.Component<Props, State>
  implements ConsoleEventObserver {
  private lastMsg: RefObject<HTMLDivElement>;

  constructor(props: Props, state: State) {
    super(props);
    this.invertVisibility = this.invertVisibility.bind(this);
    this.onConsoleEvent = this.onConsoleEvent.bind(this);
    this.lastMsg = React.createRef();
    this.state = {
      consolelog: [],
      visible: true,
    };
  }

  public render() {
    // Helper to determine the visibilty of the console
    const genVisibilityString: (collapsed: boolean) => string = collapsed =>
      collapsed ? 'none' : '';

    //Set visiblity for the console, the consoleRestoreDiv and the consoleCollapseDiv
    const consoleStyleModForRestore = {
      display: genVisibilityString(this.props.visible),
    };

    const consoleStyleModForCollapse = {
      display: genVisibilityString(!this.props.visible),
    };

    return (
      <>
        {/*Div which onClicks restores the console*/}
        <div
          className="consoleRestoreHandle"
          style={consoleStyleModForRestore}
          onClick={this.invertVisibility}
        >
          <div className="consoleLable">Log</div>

          <FontAwesome name="angle-up" className="consoleRestoreHandleIcon" />
        </div>

        {/*Div which onClicks collapses the console*/}
        <div
          className="consoleRestoreHandle"
          style={consoleStyleModForCollapse}
          onClick={this.invertVisibility}
        >
          <div className="consoleLable">Log</div>
          <FontAwesome name="angle-down" className="consoleRestoreHandleIcon" />
        </div>

        {/*Actual console div */}
        <div id="console" style={consoleStyleModForCollapse}>
          <div id="consoletext">
            {/* Console message will be rendert in this div */
            this.state.consolelog.map((text, id) => (
              <div
                id={'consolemessage ${id}'}
                ref={
                  // Set the ref lastMsg to the div containing the last console message
                  // so we can scroll to it later
                  id === this.state.consolelog.length - 1 ? this.lastMsg : null
                }
              >
                {text}
              </div>
            ))}
          </div>
        </div>
      </>
    );
  }

  /**
   * This functions sets a message and a timestap
   * in the console compontent. It also makes the
   * console visibile when a message is set.
   *
   * @param msg - that will be set in the console
   */
  public onConsoleEvent(msg: ConsoleEvent): void {
    //Create time string
    const date = new Date();
    const h = date.getHours();
    const m = date.getMinutes();
    const s = date.getSeconds();

    const timeString = `${h}:${m}:${s}`;

    // Append the message with date and time to the array of console messages
    this.setState({
      consolelog: this.state.consolelog.concat([
        `${timeString} ${msg.message}\n`,
      ]),
    });

    this.props.setVisibility(true);
  }

  /**
   * Hides the console if it is visible, displays it if it is invisible
   */
  private invertVisibility(): void {
    this.props.setVisibility(!this.props.visible);
  }

  /**
   * React callback for when the props of the component changed,
   * called after render was executed
   * {@link https://reactjs.org/docs/react-component.html#componentdidupdate}
   * Scrolls the console to the top of the last added message.
   * For that purpose messages are rendered as individual <div>
   */
  public componentDidUpdate(): void {
    if (this.lastMsg.current) {
      const msgDiv: HTMLElement = this.lastMsg.current;
      if (msgDiv.parentNode != null) {
        // Scroll to the top of the div element containing the last message
        (msgDiv.parentNode as HTMLElement).scrollTop = msgDiv.offsetTop - 450;
      }
    }
  }
}

// Structure of the properties passed to the component
interface Props {
  setVisibility: (visible: boolean) => void;
  visible: boolean;
}

// Structure of the state of the component
interface State {
  consolelog: string[];
  visible: boolean;
}
