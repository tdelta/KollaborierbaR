import React, { RefObject, ReactSVG } from 'react';
import UserIndicator from './user-indicator';
import './animals.css';
import ProjectManagement from '../../projectmanagement';
import { UsersUpdatedEvent, User} from '../../network';

export default class Usernames extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.getArray = this.getArray.bind(this);
    this.state = {
      userindicators: []
    };
  }

  public getArray(event: UsersUpdatedEvent) {
    this.setState({ userindicators: event.users })
  }

  public render() {
    return (
      <>
        {this.state.userindicators.map(iterator => (
          <UserIndicator firstName={iterator.firstName} lastName={iterator.lastName} crdtId={iterator.crdtId} />
        ))}
      </>
    );
  }
}
interface Props {}

interface State {
  userindicators: User[];
}
