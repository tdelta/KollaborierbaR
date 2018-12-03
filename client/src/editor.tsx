import ace, { Range } from 'ace-builds';
import * as ace_types from 'ace-builds';
import 'ace-builds/src-noconflict/theme-pastel_on_dark';

import PropTypes from 'prop-types';
import React from 'react';

import { Annotation, Diagnostic } from './diagnostics';

import './highlighting/jml.js';
import lint from './linting.js';

import './sidebar.css';
import './index.css';

export default class Editor extends React.Component<Props> {
  // Defining the types of the attributes for this class
  // The exclamation mark tells typescript not to check if this attribute gets initialized
  private editor!: any; // ACE editor object
  private markers: number[];
  private timeTest: number; // will be used to regulate interval of calling the linter
  private anchoredMarkers: AnchoredMarker[];
  private annotations: number[];

  constructor(props: Props) {
    super(props);
    this.markers = [];
    this.timeTest = 0;
    this.anchoredMarkers = [];
    this.annotations = [];
  }

  /**
   * React internal method, called when the component has rendered for the first time
   */
  public componentDidMount(): void {
    // Initialize ace in the div with the id 'editor'
    this.editor = ace.edit('editor');
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

    this.editor.on('change', () => {
      // Update the position of the existing error markers in the editor
      this.setMarkers();
    });
  }
  public componentDidUpdate(): void {
    // Called when new properties are passed down from the app component
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.setValue(this.props.text, -1);
    }
  }

  public render() {
    return <div id="editor" />;
  }

  /**
   * Function that calls lint, sending a request to the server, and passes the result to the app
   */
  private callLinter(): void {
    lint('LimitedIntegerSet', this.editor.getValue()).then(
      (diagnostics: Diagnostic[]) => {
        this.props.setDiagnostics(diagnostics);
        this.setAnchors();
      }
    );
  }

  /**
   * This function sets anchor points for the positions of all entries of this.props.diagnostics
   * so that their markers and annotations can automatically move, when the text changes
   */
  private setAnchors(): void {
    this.anchoredMarkers = [];

    // only show annotations, if there are any (valid) diagnostics
    if (
      this.props.diagnostics &&
      this.props.diagnostics.constructor === Array
    ) {
      // Process each element of array of diagonistics
      for (const diagnostic of this.props.diagnostics) {
        const range = new Range(
          diagnostic.startRow,
          diagnostic.startCol,
          diagnostic.endRow,
          diagnostic.endCol
        );

        // Create Anchors in the document. These update their position when text is edited
        range.start = this.editor.session.doc.createAnchor(range.start);
        range.end = this.editor.session.doc.createAnchor(range.end);

        const message = diagnostic.message;
        const type = diagnostic.kind.toLowerCase();

        // Add the anchors and content for this diagnostic to the anchoredMarkers Array
        this.anchoredMarkers.push({
          range,
          type,
          message,
        });
      }

      // Display the markers in the ace editor
      this.setMarkers();
    }
  }

  /**
   * This function displays markers in the editor for all members of anchoredMarkers
   */
  private setMarkers(): void {
    // Update the annotations displayed in the editor (icons on the left)
    this.editor.session.clearAnnotations();
    this.editor.session.setAnnotations(
      this.anchoredMarkers.map(this.toAnnotation)
    );
    
    for (const annotation of this.annotations) {
      this.editor.session.removeGutterDecoration(
        annotation,
        'ace_not_supported'
      );
    }
    this.annotations = [];

    // Remove all current markers displayed in the editor
    for (const marker of this.markers) {
      this.editor.session.removeMarker(marker);
    }
    this.markers = [];

    // Add markers for all anchoredMarkers
    for (const anchoredMarker of this.anchoredMarkers) {
      // Add the marker to the editor
      this.markers.push(
        this.editor.session.addMarker(
          anchoredMarker.range,
          `${anchoredMarker.type}Marker`,
          'text',
          true
        )
      );

      // Custom annotations need to be added manually
      if (anchoredMarker.type === 'not_supported') {
        const line = anchoredMarker.range.start.row;
        this.editor.session.addGutterDecoration(line, 'ace_not_supported');
        this.annotations.push(line);
      }
    }
  }

  /**
   * This function converts AnchoredMarkers to Annotations that can be put passed to ace's setAnnotations method
   * in order to create icons on the left of the editor
   * @param marker AnchoredMarker to convert
   * @return Annotation object with the same values
   */
  private toAnnotation(marker: AnchoredMarker): Annotation {
    return {
      row: marker.range.start.row,
      column: marker.range.start.column,
      text: marker.message,
      type: marker.type,
      startRow: marker.range.start.row,
      startCol: marker.range.start.column,
      endRow: marker.range.end.row,
      endCol: marker.range.end.column,
    };
  }
}

// defining the structure of this react components properties
interface Props {
  diagnostics: Diagnostic[];
  text: string;
  setText(text: string): void;
  setDiagnostics(diagnostics: Diagnostic[]): void;
}

/**
 * This structure is used to save markers in a document within ACE together with
 * their anchor points
 *
 * This means it can be used to underline sections of a document and display
 * messages with an icon in the gutter.
 *
 * If the document is edited, the marker will be moved with the document's
 * contents.
 */
interface AnchoredMarker {
  range: ace_types.Ace.Range; // used to mark a region within the editor: https://ace.c9.io/#nav=api&api=range
  type: string; // type of the marking, whether its an error, a warning, something else, ...
  message: string; // displayed message at the marker
}
