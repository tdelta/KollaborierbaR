function toAnnotation(diagnostic) {
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

  var {
    message,
    column,
    line,
    end,
    start,
    position,
    kind
  } = diagnostic;

  var type;

  switch (kind) {
    case 'ERROR':
      type = 'error';
      break;

    case 'WARNING':
      type = 'warning';
      break;

    default:
      type = 'info';
  }

  return {
    'row': line - 1,
    'column': column, //also -1 ? TODO: Check this
    'text': message,
    'type': type
  };
}

export default toAnnotation;
