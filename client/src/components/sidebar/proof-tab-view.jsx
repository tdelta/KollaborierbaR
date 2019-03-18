import React from 'react';
import ProofResults from '../../key/netdata/ProofResults';
import ProofNode from '../../key/prooftree/ProofNode';
import ProofTreeView from './proof-tree-view';

import Select from 'react-select';
import GuiProofNode from './gui-proof-node';
//import { ValueType }  from 'react-select/lib/types';

export default class ProofTabView extends React.Component /*<Props, State>*/ {
  constructor(props /*: Props*/) {
    super(props);

    this.state = {
      selectedNode: [],
      selectedOption: '',
    };
  }

  // public handleChange(selectedOption: ValueType<{ value: string; label: string; }>){
  //     this.setState({ selectedOption });
  //     alert("Eine neue Option wurde gesetzt:" + selectedOption);
  //     console.log(`Option selected:`, selectedOption);
  // }

  handleChange = selectedOption => {
    this.setState({ selectedOption });

    //Hier muss noch die von Anton übergegebene Funktion aufgerufen werden.
    //this.props.onMethodSelect();
    console.log('The update funtion of the dropdown menu was called');
    console.log(`Option selected:`, selectedOption);

    // So bekommt man Zugriff auf label und value
    //console.log(selectedOption.value);
  };

  render() {
    let proofs = [this.props.proofResults, this.props.proofResults];

    // React-select provides an API to style the reactcomponent
    // https://react-select.com/styles
    const ownStyle = {
      option: (provided, state) => ({
        color: '#757575',
      }),
    };

    return (
      <>
        Contract selection: <br />
        <div id="dropdown">
          <Select
            value={this.state.selectedOption}
            onChange={this.handleChange}
            options={this.props.methods}
            placeholder={'No contract selected'}
            styles={ownStyle}
          />
        </div>
        <hr />
        Current Proof: <br />
        <ProofTreeView
          proofResults={this.props.proofResults}
          displaySequent={this.props.displayFormula}
        />
        <hr />
        History: <br />
        {/* {proofs.map(proof =>
        <ProofTreeView
        proofResults={this.props.proofResults}
        displaySequent={this.props.displayFormula}
        />)
        } */}
      </>
    );
  }
}

// Brauche ich vielleicht nochmal für Typescript
// // defining the structure of this react components properties
// interface Props {
//     methods: String[];
//     proofResults: ProofResults;
//     displayFormula: (sequent: string) => void;
// }

// interface State {
//     selectedNode: ProofNode[];
//     selectedOption: String;
// }
