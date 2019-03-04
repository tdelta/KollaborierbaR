import React from 'react';

import '@fortawesome/fontawesome-free/css/all.min.css';

import GoalNode from './goal-node';
import Goal from '../../goal';

export default class OpenGoalsView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);

    this.state = {
      toggledGoal: undefined,
    };

    this.toggleGoal = this.toggleGoal.bind(this);
  }

  private toggleGoal(goal: Goal): void {
    this.setState({
      toggledGoal: goal.id,
    });
    this.props.displayFormula(goal.formula);
  }

  public render() {
    // determine, whether the goals property is set and
    // contains at least one open goal. If not, the view will show an appropriate message.
    const areGoalsValid = this.props.goals && this.props.goals.length > 0; // the project property is set to something
    // ^ the project object must at least one goal

    // if there are goals, display them
    if (areGoalsValid) {
      return (
        <div>
          {// render each element within the root folder of the
          // project as FileNode
          this.props.goals.map(goal => (
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
  project: any;
  goals: Goal[];
  displayFormula: (formula: string) => void;
  
}

interface State {
  toggledGoal: number | undefined;
}
