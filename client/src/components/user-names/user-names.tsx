import React, { RefObject, ReactSVG } from 'react';
import UserIndicator from './user-indicator';
import './animals.css';
import ProjectManagement from '../../projectmanagement';
import { User } from '../../network';

export default class Usernames extends React.Component<Props, State> {
  private static instances: Usernames[] = [];

  constructor(props: Props) {
    super(props);
    this.updateUsers = this.updateUsers.bind(this);
    this.state = {
      userindicators: []
    };
    Usernames.instances.push(this);
  }

  public updateUsers(users: User[]) {
    this.setState({ userindicators: users })
  }

  public static updateAllUsers(users: User[]) {
    for (let instance of Usernames.instances) {
      instance.updateUsers(users);
    }
  }

  public render() {
    return (
      <>
        {this.state.userindicators.map((iterator, index) => (
          <UserIndicator uid={index} firstName={iterator.firstName} lastName={iterator.lastName} crdtId={iterator.crdtId} />
        ))}
      </>
    );
  }
}
interface Props {}

interface State {
  userindicators: User[];
}
