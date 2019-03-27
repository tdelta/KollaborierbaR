import React, { CSSProperties } from 'react';
import ProofsState from '../../key/ProofsState';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofTreeView from './ProofTreeView';

import ObligationResult from '../../key/netdata/ObligationResult';
import ObligationResultHistory from '../../key/ObligationResultHistory';

import Select from 'react-select';
import Option from 'react-select/lib/types';

import GuiProofNode from './gui-proof-node';
import { ValueType, OptionProps, OptionsType } from 'react-select/lib/types';
import { StylesConfig } from 'react-select/lib/styles';

/**
 * View to be shown in one tab of the sidebar.
 * It displays available proof trees for the different proof obligations,
 * see also {@link ProofTreeView}.
 *
 * It lets the user select a proof obligation using a dropdown and will then
 * display the corresponding most recent proof tree as well as the proof
 * history.
 */
export default class ProofTabView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);

    this.handleChange = this.handleChange.bind(this);

    this.state = {
      selectedNode: [],
      selectedOption: undefined,
    };
  }

  /**
   * Internal helper function which is called, whenever the user selects a
   * proof obligation from the dropdown.
   *
   * It will update the state with the selected option, such that the proof
   * trees regarding that obligation are shown.
   */
  private handleChange(selectedOption: any): void {
    if (selectedOption != null) {
      this.setState({ selectedOption });
    } else {
      this.setState({ selectedOption: undefined });
    }
  }

  /**
   * React lifecycle method, it decides, whether to rerender this component, if
   * the state or properties changed.
   *
   * Since rendering proof trees is costly, this method ensures, that the component
   * is only rerendered, if the change actually affected a field, which influences
   * the view
   *
   * See also the react documentation on
   * <a href="https://reactjs.org/docs/react-component.html#shouldcomponentupdate">
   * shouldComponentUpdate
   * </a>
   */
  public shouldComponentUpdate(nextProps: Props, nextState: State): boolean {
    // only do a shallow comparison, so that the proof tree view is not constantly updated.

    return (
      this.props.displaySequent !== nextProps.displaySequent ||
      this.props.proofsState !== nextProps.proofsState ||
      this.state.selectedOption !== nextState.selectedOption ||
      this.props.obligationIdOfLastUpdatedProof !==
        nextProps.obligationIdOfLastUpdatedProof
    );
  }

  /**
   * React lifecycle method. It is called, whenever the properties or state
   * of this component change.
   *
   * It ensures to automatically display a proof, if it just got updated.
   */
  public componentDidUpdate(prevProps: Props, prevState: State): void {
    if (
      prevProps.obligationIdOfLastUpdatedProof !==
      this.props.obligationIdOfLastUpdatedProof
    ) {
      const option = this.props.obligationOptions.find(
        e => e.value === this.props.obligationIdOfLastUpdatedProof
      );

      this.setState({
        selectedOption: option,
      });
    }
  }

  /**
   * React lifecycle rendering method.
   * {@see https://reactjs.org/docs/react-component.html#render}
   *
   * See class documentation for information on what is being rendered.
   */
  public render() {
    const thereAreProofsAvailable: boolean =
      this.props.proofsState.getAllRecentObligationResults().length > 0;

    if (thereAreProofsAvailable) {
      // React-select provides an API to style the reactcomponent
      // https://react-select.com/styles
      const ownStyle: StylesConfig = {
        option: (base: CSSProperties, state: any) => ({
          color: '#757575',
        }),
      };

      let currentHistory: ObligationResultHistory | undefined;
      if (this.state.selectedOption != null) {
        currentHistory = this.props.proofsState.getHistoryByObligationIdx(
          this.state.selectedOption.value
        );
      }

      return (
        <>
          Contract selection: <br />
          <div id="dropdown">
            <Select
              value={this.state.selectedOption as any}
              onChange={this.handleChange}
              options={this.props.obligationOptions}
              placeholder={'No contract selected'}
              styles={ownStyle}
            />
          </div>
          <hr />
          {currentHistory == null ? (
            <>Please select an option.</>
          ) : (
            <>
              <ProofTreeView
                proofTreeOperationInfo={{
                  operation: () =>
                    this.props.saveObligationResult(
                      (currentHistory as ObligationResultHistory)
                        .last as ObligationResult
                    ),
                  label: 'Save Proof',
                }}
                obligationResult={currentHistory.last}
                displaySequent={this.props.displaySequent}
              />
              <hr />
              {currentHistory.saved.length <= 0 ? (
                <>No proofs saved in history.</>
              ) : (
                <>
                  History: <br />
                  {currentHistory.saved.map((savedResult, idx) => (
                    <ProofTreeView
                      proofTreeOperationInfo={{
                        operation: () =>
                          this.props.deleteObligationResult(
                            savedResult.obligationIdx,
                            idx + 1
                          ),
                        label: 'Remove Proof from History',
                      }}
                      obligationResult={savedResult}
                      displaySequent={this.props.displaySequent}
                    />
                  ))}
                </>
              )}
            </>
          )}
        </>
      );
    } else {
      return <>No proofs available.</>;
    }
  }
}

// defining the structure of this react components properties
interface Props {
  /**
   * options shown in the dropdown, value should equal the obligation index
   * and label determines the rendered string for the option
   */
  obligationOptions: { value: number; label: string }[];
  /** all currently available proofs */
  proofsState: ProofsState;
  /** obligation index of the most recently updated proof */
  obligationIdOfLastUpdatedProof: number | undefined;
  // callbacks needed by the nested {@link ProofTreeView}. see their documentation for more information
  displaySequent: (sequent: string) => void;
  saveObligationResult: (obligationResult: ObligationResult) => void;
  deleteObligationResult: (obligationIdx: number, historyIdx: number) => void;
}

interface State {
  /** which node is currently selected by the user (using mouse or arrow keys) */
  selectedNode: ProofNode[];
  /** which obligation id is currently selected in the dropdown? */
  selectedOption: { value: number; label: string } | undefined;
}
