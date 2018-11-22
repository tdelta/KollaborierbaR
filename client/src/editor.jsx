import React from 'react';
import PropTypes from 'prop-types';

import lint from './linting.js';
import toAnnotation from './diagnostics.js';

import Sidebar from './sidebar.jsx';

import brace from 'brace'; 
import 'brace/theme/monokai';

import './highlighting/jml.js';

import './index.css';
import './sidebar.css';

export default class Editor extends React.Component {
    callLinter(){
        lint('LimitedIntegerSet', this.editor.getValue())
            .then((diagnostics) => {
                this.props.setDiagnostics(diagnostics);
            });
    }

    // Function that sets and updates the annotations and markers
    setAnnotations(){
        // only show annotations, if there are any (valid) diagnostics
        if (this.props.diagnostics && this.props.diagnostics.constructor === Array) {
            // Transforms and sets the existing diagnostics to a format, which is compatible to Ace
            let aceDiagnostics = this.props.diagnostics.map(toAnnotation);
            this.editor.getSession().setAnnotations(aceDiagnostics);

            // Removes existing marker in the editor
            for (let i = 0; i < this.markers.length; i++) {
                this.editor.session.removeMarker(this.markers[i]);
            }

            this.markers = [];

            // Processs each element of array of aceDiagonistics
            for (let i = 0; i < aceDiagnostics.length; i++) {
                const startRow = aceDiagnostics[i]['startRow'];
                const startCol = aceDiagnostics[i]['startCol'];
                const endRow = aceDiagnostics[i]['endRow'];
                const endCol = aceDiagnostics[i]['endCol'];

                // Imports Range object
                var Range = brace.acequire('ace/range').Range;

                //Creates marker depending on the error type
                if (aceDiagnostics[i]['type'] === 'error')
                    this.markers.push(this.editor.session.addMarker(new Range(startRow, startCol, endRow, endCol), 'errorMarker', 'text'));
                else
                    this.markers.push(this.editor.session.addMarker(new Range(startRow, startCol, endRow, endCol), 'warningMarker', 'text'));
            }
        }

    }

    componentDidMount(){
        this.editor = brace.edit('editor');
        this.markers = [];
        this.timeTest = null;
        this.editor.setOptions({
            autoScrollEditorIntoView: true,
            fontSize: 20,
            firstLineNumber: 1,
        });
        this.editor.getSession().setMode('ace/mode/jml');
        this.editor.setTheme('ace/theme/monokai');
        this.editor.$blockScrolling = Infinity;

        // editor event handlers
        this.editor.on('change', () => {
            this.props.setText(this.editor.getValue());
        });

        this.editor.on('change', () => {
            clearTimeout(this.timeTest);
            this.timeTest = setTimeout(() => {this.callLinter();}, 1000);
        });
    }    

    componentDidUpdate(){
        // Wird aufgerufen, wenn React eine property, z.B. text oder diagnostics verändert
        this.setAnnotations();

        if(this.props.text !== this.editor.getValue()){
            this.editor.setValue(this.props.text,-1);
        }
    }

    render() {
        return (
            <div id="mainContainer">
                <Sidebar
                    project={this.props.project}
                    onOpenFile={(path) => alert(path.join('/'))}
                >
                    <div id="editor">
                    </div>
                </Sidebar>
            </div>
        );
    }
}

Editor.propTypes = {
    setText: PropTypes.func.isRequired,
    setDiagnostics: PropTypes.func.isRequired,
    diagnostics: PropTypes.array,
    text: PropTypes.string,
    project: PropTypes.shape({
        'name': PropTypes.string,
        'contents': PropTypes.arrayOf(PropTypes.object)
    })
};
