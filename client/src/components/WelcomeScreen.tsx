import React from 'react';

import './WelcomeScreen.css';

import Project from '../Project';
import KollaborierbarLogo from '../kollaborierbarLogo.svg';

/**
 * Component used to replace the Editor, if there is nothing to edit.
 *
 * It displays the KollaborierbaR logo and some text, informing the user that
 * they should open a project / file (depends on whether a project has already
 * been opened).
 */
export default class WelcomeScreen extends React.Component<Props, {}> {
  /**
   * React lifecycle rendering method.
   * {@see https://reactjs.org/docs/react-component.html#render}
   *
   * See constructor documentation for information on what is being rendered.
   */
  public render(): React.ReactNode {
    // Asks user to open project, if there is no project name set, asks them to
    // open a file otherwise
    const openString =
      (this.props.project as any).name != null ? 'file' : 'project';

    return (
      <>
        <div className="welcomeScreenContainer">
          <div className="welcomeLogoContainer">
            <img src={KollaborierbarLogo} className="welcomeLogo" />

            <p className="welcomeMessage">
              <span className="welcomeBigBrace">{'{'}</span>
              <span className="welcomeMessageSmallerText">
                {` please open a ${openString} `}
              </span>
              <span className="welcomeBigBrace">{'}'}</span>
            </p>
          </div>
        </div>
      </>
    );
  }
}

interface Props {
  /** Either an empty object, or the currently open project */
  project: {} | Project;
}
