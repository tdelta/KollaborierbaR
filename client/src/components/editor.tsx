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
  private anchoredMarkers: AnchoredMarker[];
  private anchoredHighlightings: AnchoredMarker[];
  private annotations: number[];

  constructor(props: Props) {
    super(props);
    this.markers = [];
    this.timeTest = 0;
    this.anchoredMarkers = [];
    this.anchoredHighlightings = [];
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

    this.editor.on('change', (delta: any) => {
      this.anchoredHighlightings.forEach(h => h.onChange(delta));
      this.anchoredMarkers.forEach(m => m.onChange(delta));
      // Update the position of the existing error markers in the editor
      this.setMarkers();
    });
    this.addKeyAnnotationType(this.editor.renderer.$gutterLayer);
  }

  public componentDidUpdate(prevProps: Props): void {
    // Called when new properties are passed down from the app component
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.ignoreChanges = true;
      this.editor.setValue(this.props.text, -1);
      this.editor.ignoreChanges = false;
      this.editor.sess
      for (const marker of this.dynamicMarkers) {
        this.editor.session.removeMarker(marker);
      }
      for (const marker of this.markers){
        this.editor.session.removeMarker(marker);
      }
      this.anchoredMarkers = [];
      this.anchoredHighlightings = [];
      this.markers = [];
      this.dynamicMarkers = [];
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
  public render() {
    return <div id="editor" />;
  }

  /**
   * Function that calls lint, sending a request to the server, and passes the result to the app
   */
  private callLinter(): void {
    let filename: string = this.props.filepath[this.props.filepath.length - 1];
    lint(filename, this.editor.getValue()).then(
      (diagnostics: Diagnostic[]) => {
        this.props.setDiagnostics(diagnostics);
        this.setAnchors();
      }
    );
  }

  private dynamicMarkers: number[] = [];

  public addBackMarker(start: any, end: any, uid: number, name: string) {
    const range = Range.fromPoints(start, end);
    const type: string = `n${uid} highlighting`;
    this.dynamicMarkers.forEach(m => this.editor.session.removeMarker(m));
    this.anchoredHighlightings = this.anchoredHighlightings.filter(m => !m.deleted);
    this.anchoredHighlightings
      .filter(m => m.type === type)
      .filter(m => parseFloat(m.message.split('|')[1]) > 0.1)
      .forEach(m => m.message = m.message.split('|')[0]+'|'+(parseFloat(m.message.split('|')[1])-0.02));

    this.anchoredHighlightings = addToArray(
      this.anchoredHighlightings,
      range,
      name+'|0.5',
      type,
      this.editor.session
    );

    if(this.anchoredHighlightings.length > 5){
      this.anchoredHighlightings.splice(0,this.anchoredHighlightings.length - 5);
    }

    for (const anchoredRange of this.anchoredHighlightings) {
      const popoverMarker: PopoverMarker = new PopoverMarker(
        anchoredRange,
        anchoredRange.message.split('|')[0],
        parseFloat(anchoredRange.message.split('|')[1])
      );
      this.dynamicMarkers.push(
        this.editor.session.addDynamicMarker(popoverMarker).id
      );
    }
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
      this.props.diagnostics.sort(diagnosticPriority);
      this.anchoredMarkers = [];
      // Process each element of array of diagonistics
      for (const diagnostic of this.props.diagnostics) {
        // Add the anchors and content for this diagnostic to the anchoredMarkers Array
        this.anchoredMarkers = addToArray(
          this.anchoredMarkers,
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
   * This function displays markers in the editor for all members of anchoredMarkers
   */
  private setMarkers(): void {
    // Remove all current markers displayed in the editor
    for (const marker of this.markers) {
      this.editor.session.removeMarker(marker);
    }
    this.markers = [];
    // Add markers for all anchoredMarkers
    this.processMarkerArray(this.anchoredMarkers, true);
  }

  /**
   * Helper function for setMarkers
   */
  private processMarkerArray(
    anchoredMarkers: AnchoredMarker[],
    front: boolean
  ) {
    for (let i = 0; i < anchoredMarkers.length; i = i + 1) {
      // Add the marker to the editor
      this.markers.push(
        this.editor.session.addMarker(
          anchoredMarkers[i].getRange(this.editor.session),
          `${anchoredMarkers[i].type}Marker`,
          'text',
          front
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
