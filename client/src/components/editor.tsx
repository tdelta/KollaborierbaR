import brace from 'brace';
import 'brace/theme/pastel_on_dark';
import PropTypes from 'prop-types';
import React from 'react';
import toAnnotation, { Annotation, Diagnostic } from '../diagnostics';
import '../highlighting/jml.js';
import '../index.css';
import lint from '../linting.js';
import './sidebar/sidebar.css';

export default class Editor extends React.Component<Props> {
  // Defining the types of the attributes for this class
  // The exclamation mark tells typescript not to check if this attribute gets initialized
  private editor!: brace.Editor;
  private markers: number[];
  private timeTest: number;

  constructor(props: Props) {
    super(props);
    this.markers = [];
    this.timeTest = 0;
  }

  public componentDidMount(): void {
    // Initialize ace in the div with the id 'editor'
    this.editor = brace.edit('editor');
    this.editor.setOptions({
      autoScrollEditorIntoView: true,
      fontSize: 20,
      firstLineNumber: 1,
    });
    this.editor.getSession().setMode('ace/mode/jml');
    this.editor.setTheme('ace/theme/pastel_on_dark');
    this.editor.$blockScrolling = Infinity;

    // editor event handlers
    this.editor.on('change', () => {
      // pass the text in the editor up to the app component
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
  }

  public componentDidUpdate(): void {
    // Called when new properties are passed down from the app component
    this.setAnnotations();
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.setValue(this.props.text, -1);
    }
  }

  public render() {
    return <div id="editor" />;
  }

  // Function that calls lint, sending a request to the server, and passes the result to the app
  private callLinter(): void {
    lint('LimitedIntegerSet', this.editor.getValue()).then(
      (diagnostics: Diagnostic[]) => {
        this.props.setDiagnostics(diagnostics);
      }
    );
  }

  // Function that sets and updates the annotations and markers
  private setAnnotations(): void {
    // only show annotations, if there are any (valid) diagnostics
    if (
      this.props.diagnostics &&
      this.props.diagnostics.constructor === Array
    ) {
      // Transforms and sets the existing diagnostics to a format, which is compatible to Ace
      const aceDiagnostics = this.props.diagnostics.map(toAnnotation);
      this.editor.getSession().setAnnotations(aceDiagnostics);

      // Removes existing marker in the editor
      for (const marker of this.markers) {
        this.editor.session.removeMarker(marker);
      }

      this.markers = [];

      // Processs each element of array of aceDiagonistics
      for (const diagnostic of aceDiagnostics) {
        const startRow: number = diagnostic.startRow;
        const startCol: number = diagnostic.startCol;
        const endRow: number = diagnostic.endRow;
        const endCol: number = diagnostic.endCol;

        // Imports Range object
        const Range = brace.acequire('ace/range').Range;

        // Creates marker depending on the error type
        if (diagnostic.type === 'error') {
          this.markers.push(
            this.editor.session.addMarker(
              new Range(startRow, startCol, endRow, endCol),
              'errorMarker',
              'text',
              true
            )
          );
        } else {
          this.markers.push(
            this.editor.session.addMarker(
              new Range(startRow, startCol, endRow, endCol),
              'warningMarker',
              'text',
              true
            )
          );
        }
      }
    }
  }
}

// defining the structure of this react components properties
interface Props {
  diagnostics: Diagnostic[];
  text: string;
  setText(text: string): void;
  setDiagnostics(diagnostics: Diagnostic[]): void;
}
