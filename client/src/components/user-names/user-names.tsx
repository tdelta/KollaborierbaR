import React, { RefObject, ReactSVG } from 'react';
import UserIndicator from './user-indicator';
import './animals.css';
import ProjectManagement from '../../projectmanagement';
import { User } from '../../collaborative/ProjectSyncController';

export default class Usernames extends React.Component<Props, State> {
  /**
   * Provides static access to the current Usernames
   */
  private static instance: Usernames | undefined;

  constructor(props: Props) {
    super(props);
    this.state = {
      userindicators: [],
    };
    Usernames.instance = this;
  }

  /**
   * Update the displayed User names of a project.
   * This static method is used by the projectmanagement.ts file because it has
   * no direct pointer to the instance
   * @param users - the users that should be displayed in the top bar
   */
  public static updateUsers(users: User[]) {
    if (Usernames.instance) {
      Usernames.instance.setState({ userindicators: users });
    }
  }

  public render() {
    return (
      <>
        {this.state.userindicators.map((iterator, index) => (
          <UserIndicator
            key={index}
            uid={index}
            firstName={iterator.firstName}
            lastName={iterator.lastName}
            crdtId={iterator.crdtId}
          />
        ))}
      </>
    );
  }
}

interface Props {}

interface State {
  userindicators: User[];
}
