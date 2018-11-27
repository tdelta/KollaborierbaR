
enum Kind {
    WARNING, ERROR, NOTE
}

interface Diagnostic {
    message: string,
    column: number,
    line: number,
    end: number,
    start: number,
    position: number,
    startRow : number,
    startCol : number,
    endRow : number,
    endCol : number,
    kind: Kind
}

enum AnnotationType {
    error, warning, info
}

interface Annotation {
    row: number,
    column: number,
    text: string,
    type: AnnotationType,
    startRow : number,
    startCol : number,
    endRow : number,
    endCol : number
}

function toAnnotation(diagnostic: Diagnostic) : Annotation {
    /* server format of diagnostics

      {
        "message": "not a statement",
        "column": 17,
        "line": 4,
        "end": 103,
        "start": 100,
        "position": 100,
        "kind":"ERROR"
      }

      annotations format:

      {
        row: 3, //line -1 !
        column: 17,
        text: "not a statement",
        type: "error"     // alternatives: 'info' or 'warning', see https://github.com/ajaxorg/ace/blob/9b5b63d1dc7c1b81b58d30c87d14b5905d030ca5/lib/ace/edit_session.js
      }
    */

    let {
        message,
        column,
        line,
        /*end,
        start,
        position,*/
        startRow,
        startCol,
        endRow,
        endCol,
        kind
    } = diagnostic;

    let type: AnnotationType;

    switch (kind) {
      case Kind.ERROR:
        type = AnnotationType.error;
        break;

      case Kind.WARNING:
        type = AnnotationType.warning;
        break;

      default:
        type = AnnotationType.info;
    }

    /*annotations format:

      {
        row: 3, //line -1 !
        column: 17,
        text: "not a statement",
        type: "error"     // alternatives: 'info' or 'warning', see https://github.com/ajaxorg/ace/blob/9b5b63d1dc7c1b81b58d30c87d14b5905d030ca5/lib/ace/edit_session.js
      }
    */

    return {
        'row': line - 1,
        'column': column, //also -1 ? TODO: Check this
        'text': message,
        'type': type,
        'startRow': startRow,
        'startCol': startCol,
        'endRow' : endRow,
        'endCol': endCol
    };
}

export default toAnnotation;
