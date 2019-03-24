package linter;

import java.io.Reader;
import javax.tools.JavaFileObject;

/** Holds diagnostic information regarding an error, warning etc. within a source code file. */
public class Diagnostic {
  final String message;
  final long end;
  final long start;
  final long startRow;
  final long startCol;
  final long endRow;
  final long endCol;
  final Kind kind;

  /** Indicates type of error */
  public enum Kind {
    ERROR,
    WARNING,
    NOTE,
    NOT_SUPPORTED // indicates a java feature, which is not supported by KeY
  }

  public Diagnostic(
      final String message,
      final long start,
      final long end,
      final JavaFileObject source,
      final Kind kind) {
    this.message = message;
    this.end = end;
    this.start = start;
    this.kind = kind;

    {
      final RowColPosition pos = getRowCol(source, start);

      this.startRow = pos.row;
      this.startCol = pos.column;
    }

    {
      final RowColPosition pos = getRowCol(source, end);

      this.endRow = pos.row;
      this.endCol = pos.column;
    }
  }

  private class RowColPosition {
    final long row;
    final long column;

    RowColPosition(final long row, final long column) {
      this.row = row;
      this.column = column;
    }
  }

  /**
   * Calculates row and column of a character within a file, given its offset from the beginning of
   * the file.
   *
   * <p>Will return -1 on (IO) errors
   *
   * @param source file the position is referencing
   * @param position offset from the start of given file
   * @return Row/Column position computed from an offset position
   */
  private RowColPosition getRowCol(final JavaFileObject source, final long position) {
    // We start at the first column and first row
    long seenRows = 0;
    long seenCols = 0;

    // We need to keep track of carriage return ('\r') later on,
    // if we are dealing with files with non-unix line endings.
    boolean lastCharacterWasCarriageReturn = false;

    try {
      final Reader r = source.openReader(true); // true == ignore encoding errors

      // We are going to traverse the file, to the given position.
      //
      // While doing that, we will count rows for each line termination sequence.
      // A line termination sequence can be one of the following:
      //
      // * "\n"
      // * "\r"
      // * "\r\n"
      //
      // We will also count the current column for each character in the current
      // row. Therefore, if we detect a line termination, we will reset that
      // counter.
      for (long seenCharacters = 0; // we need to count the seen characters...
          seenCharacters < position; // ...up to position
          ++seenCharacters) {
        final int currentCharacter = r.read();
        final boolean characterIsCarriageReturn = currentCharacter == '\r';
        final boolean characterIsLineFeed = currentCharacter == '\n';

        // A newline always means a new line, so does a carriage return
        if (characterIsLineFeed || characterIsCarriageReturn) {
          // only increment seen rows on \n, if last character was not a carriage return
          // otherwise, its a DOS line termination and we dont want to count
          // two rows
          if (!lastCharacterWasCarriageReturn | !characterIsLineFeed) {
            ++seenRows;
          }

          // reset columns, since we have begun a new line
          seenCols = 0;
        } else {
          // for each non line termination character, count it as a column
          ++seenCols;
        }

        // remember, whether last character was a carriage return
        if (characterIsCarriageReturn) {
          lastCharacterWasCarriageReturn = characterIsCarriageReturn;
        }
      }

      return new RowColPosition(seenRows, seenCols);
    } catch (final Exception e) {
      // TODO: Deal with exceptions properly

      e.printStackTrace();

      return new RowColPosition(-1, -1);
    }

    /*
    long row, column = -1;
    long positionCounter = position;

    String line;

    try {
      final LineNumberReader r = new LineNumberReader(
          source.openReader(true) //true == ignore encoding errors
      );

      line = r.readLine();
      // this loop counts all characters in the lines up to position
      while (positionCounter > line.length()) {
        // The position is not in the current line;
        //
        // substract characters in the line to count and 2 characters for
        // newline
        positionCounter -= line.length() + 2;
        line = r.readLine();
      }
      column = positionCounter;
    } catch (Exception e) {
      row = -1;
      column = -1;
      long[] results = { row, column };
      return results;
    }

    row = r.getLineNumber() - 1;
    long[] results = { row, column };

    return results;
    */
  }

  public String getMessage() {
    return message;
  }

  public Kind getKind() {
    return kind;
  }

  public long getStartRow() {
    return startRow;
  }

  public long getStartCol() {
    return startCol;
  }

  public long getEndRow() {
    return endRow;
  }

  public long getEndCol() {
    return endCol;
  }
}
