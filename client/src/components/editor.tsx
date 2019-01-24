import ace, { Range } from 'ace-builds';
import * as ace_types from 'ace-builds';
import 'ace-builds/src-noconflict/theme-pastel_on_dark';

import PropTypes from 'prop-types';
import React from 'react';

import { Annotation, Diagnostic } from '../diagnostics';

import '../highlighting/jml.js';
import lint from '../linting.js';

import './sidebar/sidebar.css';
import '../index.css';

import TextPosition from '../collaborative/TextPosition';
import AnchoredMarker from './AnchoredMarker'

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

    this.editor.on('change', () => {
      // Update the position of the existing error markers in the editor
      this.setMarkers();
    });

    this.addKeyAnnotationType(this.editor.renderer.$gutterLayer);
  }

  public componentDidUpdate(): void {
    // Called when new properties are passed down from the app component
    // only update the text if it actually changed to prevent infinite loops
    if (this.props.text !== this.editor.getValue()) {
      this.editor.ignoreChanges = true;
      this.editor.setValue(this.props.text,-1);
      this.editor.ignoreChanges = false;
    }
    //this.setAnnotations();
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
    lint(this.props.filename, this.editor.getValue()).then(
      (diagnostics: Diagnostic[]) => {
        this.props.setDiagnostics(diagnostics);
        this.setAnchors();
      }
    );
  }

  public addBackMarker(start: any, end: any, uid: number){ 
    let range = new Range(
      start.row,
      start.column,
      end.row,
      end.column
    );
    for (let j = 0; j < this.anchoredHighlightings.length; j = j + 1) {
      // Dont add the marker if it overlaps with another marker
      if (
        range.intersects(
          this.anchoredHighlightings[j].getRange(this.editor.session)
        )
      ) {
        return;
      }
    }
    const type: string = `n${uid} highlighting`;
    const message: string = '';

    this.anchoredHighlightings.push(new AnchoredMarker(
        range,
        type,
        message,
        this.editor.session
      )
    );
    this.setMarkers();
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

        // Add the anchors and content for this diagnostic to the anchoredMarkers Array
        this.anchoredMarkers.push(new AnchoredMarker(
          new Range(diagnostic.startRow,diagnostic.startCol,diagnostic.endRow,diagnostic.endCol),
          diagnostic.kind.toLowerCase(),
          diagnostic.message,
          this.editor.session
        ));
      }

      this.editor.session.clearAnnotations();
      this.editor.session.setAnnotations(
        this.anchoredMarkers.map((m) => { m.toAnnotation(this.editor.session)})
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
    this.processMarkerArray(this.anchoredMarkers,true);
    this.processMarkerArray(this.anchoredHighlightings,false);
  }

  /**
   * Helper function for setMarkers
   */
  private processMarkerArray(anchoredMarkers: AnchoredMarker[],front: boolean){
    addLoop: for (let i = 0; i < anchoredMarkers.length; i = i + 1) {
      for (let j = i + 1; j < anchoredMarkers.length; j = j + 1) {
        // Dont add the marker if it overlaps with another marker
        if (
          anchoredMarkers[i].getRange(this.editor.session).intersects(
            anchoredMarkers[j].getRange(this.editor.session)
          )
        ) {
          continue addLoop;
        }
      }
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
  filename: string;
  setText(text: string): void;
  setDiagnostics(diagnostics: Diagnostic[]): void;
}
