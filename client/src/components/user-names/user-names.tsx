import React, { RefObject, ReactSVG } from 'react';
import UserIndicator from './user-indicator'
import {UserIndicatorData} from './user-indicator-data'
import './animals.css';
import ProjectManagement from '../../projectmanagement';

export default class Usernames extends React.Component<Props, State> {
    constructor(props: Props) {
        super(props);
      this.state = {
        userindicators: []
      };

  }

  public componentDidMount(){
    this.getArray();
    this.render();
  }

private getArray(){
    return ProjectManagement.getUsernames().then((userindicators: UserIndicatorData[]) => 
      this.setState({userindicators: userindicators})
    );
  }

public render(){
  return( 
    <>
                {
                    this.state.userindicators.map((iterator) =>
                      <UserIndicator name={iterator.name} color={iterator.color}/>
                    )
                } 
    </>
  );
}
}
interface Props{

}

interface State{
  userindicators: UserIndicatorData[]
}


