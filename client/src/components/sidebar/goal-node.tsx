import React from 'react';

import './sidebar.css';

import FontAwesome from 'react-fontawesome';

import OpenGoalInfo from '../../key/netdata/OpenGoalInfo';

export default class GoalNode extends React.Component<Props, {}> {
  constructor(props: Props) {
    super(props);

    this.handleDoubleClick = this.handleDoubleClick.bind(this);
  }

  public render() {
    const label = (
      <>
        <FontAwesome name="flag-checkered" className="goalNodeIcon" /> (
        {this.props.goal.id}) {this.props.goal.sequent}
      </>
    );

    const background = this.props.toggled
      ? 'activeFileNode'
      : 'inactiveFileNode';

    return (
      <div onDoubleClick={this.handleDoubleClick} className={background}>
        {label}
      </div>
    );
  }

  private handleDoubleClick() {
    this.props.toggleGoal(this.props.goal);
  }
}

interface Props {
  goal: OpenGoalInfo;
  toggled: boolean;
  toggleGoal: (goal: OpenGoalInfo) => void;
}
