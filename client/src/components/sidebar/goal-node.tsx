import React from 'react';

import './sidebar.css';

import FontAwesome from 'react-fontawesome';

import OpenGoalInfo from '../../key/netdata/OpenGoalInfo';

/**
 * This component is a signle open goal node of a proof.
 * It is created by the openGoalView component.
 *
 */
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

  /**
   * This function calls toogleGoal from props and thus
   * displays the sequent of the open goal.
   */
  private handleDoubleClick() {
    this.props.toggleGoal(this.props.goal);
  }
}

interface Props {
  /** Contains all important information about the open goal (sequent, id) */
  goal: OpenGoalInfo;
  /** boolean whether the sequent is displayed at the moment */
  toggled: boolean;
  /** function which will when called display the sequent of the open goal */
  toggleGoal: (goal: OpenGoalInfo) => void;
}
