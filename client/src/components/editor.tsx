import ace, { Range } from 'ace-builds';
import * as ace_types from 'ace-builds';
import 'ace-builds/src-noconflict/theme-pastel_on_dark';
import 'ace-builds/src-noconflict/ext-language_tools';

import PropTypes from 'prop-types';
import React from 'react';

import CollabController from '../collaborative/CollabController';

import { ContextMenu, MenuItem, ContextMenuTrigger } from 'react-contextmenu';

import {
  Annotation,
  Diagnostic,
  toAnnotation,
  diagnosticPriority,
} from '../diagnostics';

import AnchoredMarker, { addToArray, split } from './AnchoredMarker';
import PopoverMarker from './PopoverMarker';

import '../highlighting/jml.js';
import '../highlighting/macro.mjs';
import '../highlighting/sequent.js';
import lint from '../linting.js';

import './sidebar/sidebar.css';
import '../index.css';

export default class Editor extends React.Component<Props, State> {
  // Defining the types of the attributes for this class
  // The exclamation mark tells typescript not to check if this attribute gets initialized
  public editor!: any; // ACE editor object
  private markers: number[];
  private timeTest: number; // will be used to regulate interval of calling the linter
  private errorMarkers: AnchoredMarker[];
  private popoverMarkers: AnchoredMarker[];
  private errorMarkerIds: number[];
  private popoverMarkerIds: number[];
  private obligationAnnotations: Annotation[] = [];

  constructor(props: Props) {
    super(props);
    this.markers = [];
    this.timeTest = 0;
    this.errorMarkers = [];
    this.popoverMarkers = [];
    this.errorMarkerIds = [];
    this.popoverMarkerIds = [];
    this.state = {
      disableContext: true,
      contracts: [],
    };

    this.simulateTextReplace = this.simulateTextReplace.bind(this);
  }

  /**
   * React internal method, called when the component has rendered for the first time
   */
  public componentDidMount(): void {
    // Initialize ace in the div with the id 'editor'
    this.editor = ace.edit('editor');
    this.editor.setOptions({
      enableBasicAutocompletion: true,
      enableSnippets: true,
      enableLiveAutocompletion: true,
      autoScrollEditorIntoView: true,
      fontSize: 20,
      firstLineNumber: 1,
    });

    this.editor.setTheme('ace/theme/pastel_on_dark');
    this.editor.$blockScrolling = Infinity;

    // editor event handlers
    this.editor.on('change', () => {
      // pass the text in the editor up to the app component
      //if(!this.editor.ignoreChanges)
      this.props.setText(this.editor.getValue());
    });

    this.editor.on('change', () => {
      // call the server to lint the code after one second
      // this only happens if the method is not called again within one second
      clearTimeout(this.timeTest);
      this.timeTest = window.setTimeout(() => {
        this.callLinter();
      }, 1000);
    });

    this.editor.on('change', (delta: ace_types.Ace.Delta) => {
      if(delta.action === 'insert' && !this.editor.ignoreChanges){
        if(split(this.popoverMarkers,delta.start,this.editor.session))
        this.setPopoverMarkers();
      }
      this.popoverMarkers.forEach(h => h.onChange(delta));
      this.errorMarkers.forEach(m => m.onChange(delta));
      // Update the position of the existing error markers in the editor
      this.setMarkers();
    });

    this.editor.container.addEventListener('contextmenu', (e: any) => {
      e.preventDefault();
      // get x and y coordinates of the registered rightclick
      const lineNr: number = this.editor.getSelectionRange().start.row;
      const lineTxt: string = this.editor.session.getLines(
        0,
        this.editor.session.getLength()
      );
      // if the line of the right click contains a method declaration, get
      // the methods for it
      const contracts: number[] = this.props.getContractsForMethod(
        lineTxt,
        lineNr
      );

      // if contracts exist iniciate a state change to show the context menu
      // else disable it
      if (contracts.length) {
        this.setState({ disableContext: false, contracts: contracts });
      } else {
        this.setState({ disableContext: true, contracts: [] });
      }
    });

    this.editor.on('gutterclick', (e: any) => {
      this.props.saveFile().then(() => {
        if (
          e.domEvent.target.className.includes('obligation_todo') &&
          e.domEvent.target.firstChild
        ) {
          const rowString = e.domEvent.target.firstChild.data;
          const row = parseInt(rowString, 10) - 1;

          if (row) {
            this.editor.session.getSelection().clearSelection();
            const obligations = this.props.getObligations(
              this.editor.session.getLines(0, this.editor.session.getLength())
            );

            this.props.onProveObligations(obligations[row]);
          }
        } else if (
          e.domEvent.target.className.includes('obligation_done') &&
          e.domEvent.target.firstChild
        ) {
          const rowString = e.domEvent.target.firstChild.data;
          const row = parseInt(rowString, 10) - 1;

          if (row) {
            this.editor.session.getSelection().clearSelection();
            const obligations = this.props.getObligations(
              this.editor.session.getLines(0, this.editor.session.getLength())
            );

            this.props.resetObligation(obligations[row]);
            this.props.onProveObligations(obligations[row]);
          }
        }
      });
    });

    this.addKeyAnnotationType(this.editor.renderer.$gutterLayer);
  }

  public simulateTextReplace(text: string) {
    this.editor.setValue(text);
  }

  /**
   * Called when new properties are passed down from the app component
   * @param prevProps Properties before the update, used to detect changes
   */
  public componentDidUpdate(prevProps: Props): void {
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.ignoreChanges = true;
      this.editor.getSession().setValue(this.props.text, -1);
      this.editor.ignoreChanges = false;

      for (const marker of this.popoverMarkerIds) {
        this.editor.session.removeMarker(marker);
      }
      for (const marker of this.markers) {
        this.editor.session.removeMarker(marker);
      }
      this.errorMarkers = [];
      this.popoverMarkers = [];
      this.markers = [];
      this.popoverMarkerIds = [];
    }
    if (this.props.diagnostics !== prevProps.diagnostics) {
      this.setAnchors();
    }

    let mode = '';
    switch (this.props.filetype) {
      case 'java':
        mode = 'ace/mode/jml';
        break;
      case 'sequent':
        mode = 'ace/mode/sequent';
        break;
      case 'script':
        mode = 'ace/mode/macro';
        break;
    }
    console.log(mode);
    this.editor.getSession().setMode(mode);
    if (this.props.filetype === 'sequent') {
      this.editor.setReadOnly(true);
    } else {
      this.editor.setReadOnly(false);
    }

    this.setProofObligations();
  }

  /**
   * Evaluate the obligation information and update
   * the obligation indicators of the gutter of the editor
   */
  private setProofObligations() {
    const obligations = this.props.getObligations(
      this.editor.session.getLines(0, this.editor.session.getLength())
    );
    this.obligationAnnotations = [];
    // Iterate over the indices of the result, which correspond to the line numbers
    for (const index of Object.keys(obligations)) {
      const obligationIdx: number = obligations[index as any] as number;

      const row = parseInt(index, 10);

      const isProven: boolean = this.props.provenObligations.includes(
        obligationIdx
      );

      if (isProven) {
        this.obligationAnnotations.push({
          row: row,
          column: 0,
          text: 'Proven!',
          type: 'obligation_done',
          startRow: row,
          startCol: 0,
          endRow: row,
          endCol: 0,
        });
      } else {
        this.obligationAnnotations.push({
          row: row,
          column: 0,
          text: 'Click to prove!',
          type: 'obligation_todo',
          startRow: row,
          startCol: 0,
          endRow: row,
          endCol: 0,
        });
      }
    }

    this.updateAnnotations();
  }

  /**
   * Remove previous gutter information of the editor
   * and set new gutter information.
   */
  private updateAnnotations(): void {
    this.editor.session.clearAnnotations();
    this.editor.session.setAnnotations(
      this.props.diagnostics
        .map(toAnnotation)
        .concat(this.obligationAnnotations)
    );
  }

  /**
   * This function adds a type of annotation to the renderer of the gutter (left)
   * we could have used session.addGutterDecoration instead, but get automatically updating positions this way for free
   * @param gutterLayer the renderer to extend
   */
  private addKeyAnnotationType(gutterLayer: any) {
    // save the default implementation in a variable
    const superSetAnnotations = gutterLayer.setAnnotations;
    gutterLayer.setAnnotations = function(annotations: Annotation[]) {
      // call the default function first so we can overwrite the results
      superSetAnnotations.call(gutterLayer, annotations);
      for (const annotation of annotations) {
        if (annotation.type === 'not_supported') {
          // set a custom css class for our own error type
          const rowInfo = this.$annotations[annotation.row];
          rowInfo.className = 'ace_not_supported';
        } else if (annotation.type === 'obligation_todo') {
          // set a custom css class for our own error type
          const rowInfo = this.$annotations[annotation.row];
          rowInfo.className = 'obligation_todo';
        } else if (annotation.type === 'obligation_done') {
          // set a custom css class for our own error type
          const rowInfo = this.$annotations[annotation.row];
          rowInfo.className = 'obligation_done';
        }
      }
    };
  }

  /**
   * Called by react to display html of the component
   */
  public render() {
    let editorstyle;
    let proveAllContracts;
    // Resize the editor depening whether or not the console is visible
    if (this.props.consoleIsVisible) {
      editorstyle = {
        height: '66%',
      };
    } else {
      editorstyle = {
        height: '98%',
      };
    }
    // if there are multiple contracts add a field to the context menu to prove all of them
    if (this.state.contracts.length > 1) {
      proveAllContracts = (
        <div>
          <MenuItem divider />
          <MenuItem
            onClick={() => {
              this.props.saveFile().then(() => {
                for (const contract of this.state.contracts) {
                  this.props.resetObligation(contract);
                }
              });
              this.props.onProveObligations(this.state.contracts);
            }}
          >
            Prove all Method Contracts
          </MenuItem>
        </div>
      );
    }

    return (
      <div id="editor_container" style={editorstyle}>
        <ContextMenuTrigger
          id="sick_menu"
          holdToDisplay={-1}
          disable={this.state.disableContext}
        >
          <div id="editor" style={editorstyle} />
        </ContextMenuTrigger>

        <ContextMenu id="sick_menu">
          {/* for each contract add an entry to the context menu to prove it */}
          {this.state.contracts.map((contract, id) => (
            <MenuItem
              key={id}
              onClick={() => {
                this.props.saveFile().then(() => {
                  this.props.resetObligation(contract);
                  this.props.onProveObligations(contract);
                });
              }}
            >
              Prove Contract {id + 1}
            </MenuItem>
          ))}
          {proveAllContracts}
        </ContextMenu>
      </div>
    );
  }

  /**
   * Function that calls lint, sending a request to the server, and passes the result to the app
   */
  private callLinter(): void {
    if (this.props.filetype === 'java') {
      const filename: string = this.props.filepath[
        this.props.filepath.length - 1
      ];
      lint(filename, this.editor.getValue()).then(
        (diagnostics: Diagnostic[]) => {
          this.props.setDiagnostics(diagnostics);
          this.setAnchors();
        }
      );
    }
  }

  /**
   * Adds a marker to the array that will be displayed as a highlighted color behind the text.
   * @param start - The start position of the marker
   * @param end - The end position of the marker
   * @param uid - The id of the color to display (defined in marker-colors.css)
   * @param name - Displayed in a tooltip on hovering over the marker
   */
  public addBackMarker(start: any, end: any, uid: number, name: string) {
    const range = Range.fromPoints(start, end);
    const type: string = `n${uid} highlighting`;
    // The deleted field is set, when the range of a marker is empty
    this.popoverMarkers = this.popoverMarkers.filter(m => !m.deleted);
    let deleteOld: boolean = false;
    if(deleteOld){
      // Make old markers less opaque
      this.popoverMarkers
        .filter(m => m.type === type)
        .filter(m => m.opacity > 0.1)
        .forEach(m => (m.opacity -= 0.01));
    }
    let maxLength: number;
    if(deleteOld){
      maxLength = 10;
    } else {
      maxLength = Infinity;
    }
    this.popoverMarkers = addToArray(
      this.popoverMarkers,
      range,
      name,
      type,
      this.editor.session,
      10
    );

    // Set the opacity of the newly added anchored marker
    this.popoverMarkers[this.popoverMarkers.length - 1].opacity = 0.5;

    if(deleteOld){
      // Remove old markers
      if (this.popoverMarkers.length > 5) {
        this.popoverMarkers.splice(0, this.popoverMarkers.length - 5);
      }
    }
    this.setPopoverMarkers();
  }

  private setPopoverMarkers(): void {
    this.popoverMarkerIds.forEach(m => this.editor.session.removeMarker(m));
    for (const anchoredRange of this.popoverMarkers) {
      const popoverMarker: PopoverMarker = new PopoverMarker(
        anchoredRange,
        anchoredRange.message,
        anchoredRange.opacity
      );
      this.popoverMarkerIds.push(
        this.editor.session.addDynamicMarker(popoverMarker).id
      );
    }
  }

  /**
   * This function sets anchor points for the positions of all entries of this.props.diagnostics
   * so that their markers and annotations can automatically move, when the text changes
   */
  private setAnchors(): void {
    this.errorMarkers = [];

    // only show annotations, if there are any (valid) diagnostics
    if (
      this.props.diagnostics &&
      this.props.diagnostics.constructor === Array
    ) {
      this.props.diagnostics.sort(diagnosticPriority);
      this.errorMarkers = [];
      // Process each element of array of diagonistics
      for (const diagnostic of this.props.diagnostics) {
        // Add the anchors and content for this diagnostic to the errorMarkers Array
        this.errorMarkers = addToArray(
          this.errorMarkers,
          new Range(
            diagnostic.startRow,
            diagnostic.startCol,
            diagnostic.endRow,
            diagnostic.endCol
          ),
          diagnostic.message,
          diagnostic.kind.toLowerCase(),
          this.editor.session
        );
      }

      this.updateAnnotations();

      // Display the markers in the ace editor
      this.setMarkers();
    }
  }

  /**
   * This function displays markers in the editor for all members of errorMarkers
   */
  private setMarkers(): void {
    // Remove all current markers displayed in the editor
    for (const marker of this.markers) {
      this.editor.session.removeMarker(marker);
    }
    this.markers = [];
    // Add markers for all errorMarkers
    for (const errorMarker of this.errorMarkers) {
      // Add the marker to the editor
      this.markers.push(
        this.editor.session.addMarker(
          errorMarker.getRange(this.editor.session),
          `${errorMarker.type}Marker`,
          'text',
          false
        )
      );
    }
  }
}

// defining the structure of the state
interface State {
  disableContext: boolean;
  contracts: number[];
}

// defining the structure of this react components properties
interface Props {
  saveFile(): Promise<void>;
  diagnostics: Diagnostic[];
  provenObligations: number[];
  text: string;
  filepath: string;
  filetype: string;
  setText(text: string): void;
  setDiagnostics(diagnostics: Diagnostic[]): void;
  resetObligation(obligationIdx: number): void;
  collabController: CollabController;
  getObligations: (lines: string[]) => number[];
  getContractsForMethod: (line: string, row: number) => number[];
  onProveObligations: (nr: number | number[]) => boolean;
  consoleIsVisible: boolean;
}
