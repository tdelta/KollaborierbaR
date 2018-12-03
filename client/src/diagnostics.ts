enum Kind {
  WARNING = 'WARNING',
  ERROR = 'ERROR',
  NOTE = 'NOTE',
  NOT_SUPPORTED = 'NOT_SUPPORTED',
}

export interface Diagnostic {
  message: string;
  startRow: number;
  startCol: number;
  endRow: number;
  endCol: number;
  kind: Kind;
}

export interface Annotation {
  row: number;
  column: number;
  text: string;
  type: string;
  startRow: number;
  startCol: number;
  endRow: number;
  endCol: number;
}
