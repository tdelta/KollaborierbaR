package linter;

/** Holds diagnostic information regarding an error, warning etc. within a source code file. */
public class Diagnostic {
  final String message;
  final long column;
  final long line;
  final long end;
  final long start;
  final long position;
  final Kind kind;

  /** Indicates type of error */
  public enum Kind {
    ERROR,
    WARNING,
    NOTE
  }

  public Diagnostic(
      final String message,
      final long column,
      final long line,
      final long start,
      final long end,
      final long position,
      final Kind kind) {
    this.message = message;
    this.column = column;
    this.line = line;
    this.end = end;
    this.start = start;
    this.position = position;
    this.kind = kind;
  }

  public String getMessage() {
    return message;
  }

  public long getColumn() {
    return column;
  }

  public long getLine() {
    return line;
  }

  /** Offset of described problem from start of source file */
  public long getStart() {
    return start;
  }

  /** Offset of described problem from end of source file */
  public long getEnd() {
    return end;
  }

  /** getStart() &lt;= getPosition() &lt;= getEnd() */
  public long getPosition() {
    return position;
  }

  public Kind getKind() {
    return kind;
  }
}
