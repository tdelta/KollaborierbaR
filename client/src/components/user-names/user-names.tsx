import React, { RefObject, ReactSVG } from 'react';
import UserIndicator from './user-indicator';
import './animals.css';
import ProjectManagement from '../../projectmanagement';
import { User } from '../../collaborative/ProjectSyncController';

/**
 * UI Component for displaying user icons (circles) and names
 */
export default class Usernames extends React.Component<Props, State> {
  /**
   * Provides static access to the current Usernames
   */
  private static instance: Usernames | undefined;

  constructor(props: Props) {
    super(props);
    this.state = {
      userindicators: [],
      ownId: -1,
    };
    Usernames.instance = this;
  }

  /**
   * Update the displayed User names of a project.
   * This static method is used by the projectmanagement.ts file because it has
   * no direct pointer to the instance
   * @param users - the users that should be displayed in the top bar
   */
  public static updateUsers(users: User[], ownId: number) {
    if (Usernames.instance) {
      Usernames.instance.setState({ userindicators: users, ownId: ownId });
    }
  }

  /**
   * Get a user indicator icon for a given user
   * @param key - the unique key of the element
   * @returns the indicator icon html element
   */
  private getUserIndicator(user: User | undefined, key: number) {
    if (user) {
      return (
        <UserIndicator
          key={key}
          uid={key}
          firstName={user.firstName}
          lastName={user.lastName}
          crdtId={user.idInProject}
        />
      );
    }
  }

  /**
   * React callback that creates the html elements
   */
  public render() {
    const ownUser = this.state.userindicators.find(
      user => user.idInProject === this.state.ownId
    );
    console.log(this.state.ownId);
    const otherUsers = this.state.userindicators.filter(
      user => user.idInProject !== this.state.ownId
    );
    const divider = otherUsers.length > 0 ? <span className="divider" /> : null;
    return (
      <>
        {this.getUserIndicator(ownUser, 0)}
        {divider}
        {otherUsers.map((iterator, index) =>
          this.getUserIndicator(iterator, index + 1)
        )}
      </>
    );
  }
}

interface Props {}

interface State {
  userindicators: User[];
  ownId: number;
}
