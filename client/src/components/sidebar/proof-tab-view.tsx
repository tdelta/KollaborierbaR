import React, { CSSProperties } from 'react';
import ProofsState from '../../key/ProofsState';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofTreeView from './proof-tree-view';

import ObligationResult from '../../key/netdata/ObligationResult';
import { ObligationResultHistory } from '../../key/ProofsState';

import Select from 'react-select';
import Option from 'react-select/lib/types';

import GuiProofNode from './gui-proof-node';
import { ValueType, OptionProps, OptionsType }  from 'react-select/lib/types';
import { StylesConfig }  from 'react-select/lib/styles';

export default class ProofTabView extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);

    this.handleChange = this.handleChange.bind(this);

    this.state = {
      selectedNode: [],
      selectedOption: undefined,
    };
  }

  // Die Typdefinitionen der Library wirken inkorrekt, daher any
  public handleChange(selectedOption: any): void {
      if (selectedOption != null) {
        this.setState({ selectedOption });
      }

      else {
        this.setState({ selectedOption: undefined });
      }
  }

  public shouldComponentUpdate(nextProps: Props, nextState: State): boolean {
    // only do a shallow comparison, so that the proof tree view is not constantly updated.

    return this.props.displaySequent !== nextProps.displaySequent
        || this.props.proofsState !== nextProps.proofsState
        || this.state.selectedOption !== nextState.selectedOption
        || this.props.obligationIdOfLastUpdatedProof !== nextProps.obligationIdOfLastUpdatedProof;
  }

  public componentDidUpdate(prevProps: Props, prevState: State): void {
    if (prevProps.obligationIdOfLastUpdatedProof !== this.props.obligationIdOfLastUpdatedProof) {
      const option = this.props.methods.find(e => 
        e.value === this.props.obligationIdOfLastUpdatedProof
      );

      this.setState({
        selectedOption: option
      });
    }
  }

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

      let currentHistory: ObligationResultHistory | undefined = undefined;
      if (this.state.selectedOption != null) {
        currentHistory = this.props.proofsState
          .getHistoryByObligationIdx(this.state.selectedOption.value);
      }
      
      return (
        <>
          Contract selection: <br />
          <div id="dropdown">
            <Select
              value={this.state.selectedOption as any}
              onChange={this.handleChange}
              options={this.props.methods}
              placeholder={'No contract selected'}
              styles={ownStyle}
            />
          </div>
          <hr />
          {
            currentHistory == null ?
              <>Please select an option.</>
            : <>
                <ProofTreeView
                  saveProof= {() => this.props.saveObligationResult(
                    (currentHistory as ObligationResultHistory)
                      .last as ObligationResult
                  )
                  }
                  obligationResult={
                    currentHistory.last
                  }
                  displaySequent={this.props.displaySequent}
                />
                <hr />
                {
                  currentHistory.saved.length <= 0 ?
                    <>No proofs saved in history.</>
                  : <>
                      History: <br />
                      {
                        currentHistory.saved.map(savedResult =>
                          <ProofTreeView
                            saveProof={() => this.props.saveObligationResult(
                              (currentHistory as ObligationResultHistory)
                                .last as ObligationResult
                            )
                            }
                            obligationResult={savedResult}
                            displaySequent={this.props.displaySequent}
                          />)
                      }
                    </>
                }
              </>
          }
        </>
      );
    }

    else {
      return <>No proofs available.</>
    }
  }
}

interface Props {
    methods: {value: number, label: string}[];
    proofsState: ProofsState;
    obligationIdOfLastUpdatedProof: number | undefined;
    displaySequent: (sequent: string) => void;
    saveObligationResult: (obligationResult: ObligationResult) => void;
}

interface State {
    selectedNode: ProofNode[];
    selectedOption: {value: number, label: string} | undefined;
}
