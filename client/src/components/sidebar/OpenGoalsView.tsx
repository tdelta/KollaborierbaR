import React from 'react';

import '@fortawesome/fontawesome-free/css/all.min.css';

import GoalNode from './goal-node';
import OpenGoalInfo from '../../key/netdata/OpenGoalInfo';

import ProofsState from '../../key/ProofsState';

/**
 * This compontent renders all open goal-nodes for a
 * proof.
 */
export default class OpenGoalsView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);

    this.state = {
      toggledGoal: undefined,
    };

    this.toggleGoal = this.toggleGoal.bind(this);
  }

  /**
   * This function displays the sequent of an open
   * goal. The function is passed down to every open
   * goal node and will be called when a goal node is
   * double clicked.
   *
   * @param goal necassary information about the goal to render the sequent
   */
  private toggleGoal(goal: OpenGoalInfo): void {
    this.setState({
      toggledGoal: goal.id,
    });
    this.props.displayFormula(goal.formula);
  }

  public render() {
    const goals: OpenGoalInfo[] = this.props.proofsState
      .getAllRecentObligationResults()
      .flatMap(obligationResult => obligationResult.openGoals);

    // determine, whether the goals property is set and
    // contains at least one open goal. If not, the view will show an appropriate message.
    const areGoalsValid = goals.length > 0;

    // if there are goals, display them
    if (areGoalsValid) {
      return (
        <div>
          {goals.map(goal => (
            <GoalNode
              key={goal.id}
              // ^when rendering a list of elements, react
              // requires a unique key for all of them
              goal={goal}
              toggled={
                this.state.toggledGoal == null
                  ? false
                  : this.state.toggledGoal === goal.id
              }
              toggleGoal={this.toggleGoal}
            />
          ))}
        </div>
      );
    } else {
      // if there are no contents, a message about no open goals
      return <>No open goals.</>;
    }
  }
}

// defining the structure of this react components properties
interface Props {
  proofsState: ProofsState;
  displayFormula: (formula: string) => void;
}

interface State {
  toggledGoal: number | undefined;
}
