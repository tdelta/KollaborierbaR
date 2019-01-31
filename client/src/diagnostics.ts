// Ordered by priority
enum Kind {
  NOT_SUPPORTED = 'NOT_SUPPORTED',
  ERROR = 'ERROR',
  WARNING = 'WARNING',
  NOTE = 'NOTE',
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

export function toAnnotation(diagnostic: Diagnostic): Annotation{
  return {
    row: diagnostic.startRow,
    column: diagnostic.startCol,
    text: diagnostic.message,
    type: diagnostic.kind.toLowerCase(),
    startRow: diagnostic.startRow,
    startCol: diagnostic.startCol,
    endRow: diagnostic.endRow,
    endCol: diagnostic.endCol,
  };
}

const order: Kind[] = [Kind.NOTE, Kind.WARNING, Kind.ERROR, Kind.NOT_SUPPORTED]

export function diagnosticPriority(d1: Diagnostic, d2: Diagnostic): number {
  return order.indexOf(d1.kind) - order.indexOf(d2.kind);
}
