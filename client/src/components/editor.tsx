import ace, { Range } from 'ace-builds';
import * as ace_types from 'ace-builds';
import 'ace-builds/src-noconflict/theme-pastel_on_dark';

import PropTypes from 'prop-types';
import React from 'react';

import {
  Annotation,
  Diagnostic,
  toAnnotation,
  diagnosticPriority,
} from '../diagnostics';
import AnchoredMarker, { addToArray } from './AnchoredMarker';
import PopoverMarker from './PopoverMarker';

import '../highlighting/jml.js';
import lint from '../linting.js';

import './sidebar/sidebar.css';
import '../index.css';

export default class Editor extends React.Component<Props> {
  // Defining the types of the attributes for this class
  // The exclamation mark tells typescript not to check if this attribute gets initialized
  public editor!: any; // ACE editor object
  private markers: number[];
  private timeTest: number; // will be used to regulate interval of calling the linter
  private errorMarkers: AnchoredMarker[];
  private popoverMarkers: AnchoredMarker[];
  private errorMarkerIds: number[];
  private popoverMarkerIds: number[];

  constructor(props: Props) {
    super(props);
    this.markers = [];
    this.timeTest = 0;
    this.errorMarkers = [];
    this.popoverMarkers = [];
    this.errorMarkerIds = [];
    this.popoverMarkerIds = [];
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
      this.popoverMarkers.forEach(h => h.onChange(delta));
      this.errorMarkers.forEach(m => m.onChange(delta));
      // Update the position of the existing error markers in the editor
      this.setMarkers();
    });
    this.addKeyAnnotationType(this.editor.renderer.$gutterLayer);
  }

  /**
   * Called when new properties are passed down from the app component
   * @param prevProps Properties before the update, used to detect changes
   */
  public componentDidUpdate(prevProps: Props): void {
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.ignoreChanges = true;
      this.editor.setValue(this.props.text, -1);
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
        }
      }
    };
  }

  /**
   * Called by react to display html of the component
   */
  public render() {
    return <div id="editor" />;
  }

  /**
   * Function that calls lint, sending a request to the server, and passes the result to the app
   */
  private callLinter(): void {
    const filename: string = this.props.filepath[
      this.props.filepath.length - 1
    ];
    lint(filename, this.editor.getValue()).then((diagnostics: Diagnostic[]) => {
      this.props.setDiagnostics(diagnostics);
      this.setAnchors();
    });
  }

  /**
   * Adds a marker to the array that will be displayed as a highlighted color behind the text.
   * @param start The start position of the marker
   * @param end The end position of the marker
   * @param uid The id of the color to display (defined in marker-colors.css)
   * @param name Displayed in a tooltip on hovering over the marker
   */
  public addBackMarker(start: any, end: any, uid: number, name: string) {
    const range = Range.fromPoints(start, end);
    const type: string = `n${uid} highlighting`;
    this.popoverMarkerIds.forEach(m => this.editor.session.removeMarker(m));
    // The deleted field is set, when the range of a marker is empty
    this.popoverMarkers = this.popoverMarkers.filter(m => !m.deleted);
    // Make old markers less opaque
    this.popoverMarkers
      .filter(m => m.type === type)
      .filter(m => m.opacity > 0.1)
      .forEach(m => (m.opacity -= 0.01));

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

    // Remove old markers
    if (this.popoverMarkers.length > 5) {
      this.popoverMarkers.splice(0, this.popoverMarkers.length - 5);
    }

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
      this.editor.session.clearAnnotations();
      this.editor.session.setAnnotations(
        this.props.diagnostics.map(toAnnotation)
      );

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

// defining the structure of this react components properties
interface Props {
  diagnostics: Diagnostic[];
  text: string;
  filepath: string;
  setText(text: string): void;
  setDiagnostics(diagnostics: Diagnostic[]): void;
}
