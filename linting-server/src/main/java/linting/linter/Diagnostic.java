package linting.linter;

import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;

import javax.tools.JavaFileObject;

/**
 * Holds diagnostic information regarding an error, warning etc. within a source
 * code file.
 */
public class Diagnostic {
	final String message;
	final long column;
	final long line;
	final long end;
	final long start;
	final long position;
	final long startRow;
	final long startCol;
	final long endRow;
	final long endCol;
	final Kind kind;

	/** Indicates type of error */
	public enum Kind {
		ERROR, WARNING, NOTE
	}

	public Diagnostic(final String message, final long column, final long line, final long start, final long end,
		final long position, final JavaFileObject source, final Kind kind) {
		this.message = message;
		this.column = column;
		this.line = line;
		this.end = end;
		this.start = start;
		this.position = position;
		this.kind = kind;
		long[] pos = getRowCol(source, start);
		this.startRow = pos[0];
		this.startCol = pos[1];
		pos = getRowCol(source, end);
		this.endRow = pos[0];
		this.endCol = pos[1] +1;
	}

	private long[] getRowCol(JavaFileObject source, long position) {
		long row, column = -1;
		long count = 0;
		long truePos = position;
		LineNumberReader r = null;
		String line = null;

		try {
			
			r = new LineNumberReader(source.openReader(true));
			
			while (count < truePos) {
				column = 0;
				line = r.readLine();
				
				while (count < truePos && column < line.length()) {
					count++;
					column++;
				}
				truePos-=1;
				if (column == line.length())
					count++;

				System.out.println(r.getLineNumber() + " | " + count + " | " + position + " | " + " | " + column + "  | " + line.length());
			}
		} catch (Exception e) {
			//e.printStackTrace();
		}

		//row = (count == position) ? -1 : r.getLineNumber();
		//column = (count == position) ? -1 : column -1;
		row = r.getLineNumber() - 1;
		column = column - 1;
		long[] results = { row, column };

		return results;
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
