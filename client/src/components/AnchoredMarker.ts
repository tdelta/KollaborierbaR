import ace, { Range } from 'ace-builds';
import * as ace_types from 'ace-builds';

/**
 * This structure is used to save markers in a document within ACE together with
 * their anchor points
 *
 * This means it can be used to underline sections of a document and display
 * messages with an icon in the gutter.
 *
 * If the document is edited, the marker will be moved with the document's
 * contents.
 */
export default class AnchoredMarker {
  private start!: any; // used to mark a region within the editor
  private end!: any;
  type: string; // type of the marking, whether its an error, a warning, something else, ...
  message: string; // displayed message at the marker
  public deleted: boolean = false;

  constructor(
    range: ace_types.Ace.Range,
    message: string,
    type: string,
    editSession: ace_types.Ace.EditSession
  ) {
    this.setRange(range, editSession);
    this.type = type;
    this.message = message;
  }

  /**
   * Getter for the range of the marker
   * @param editSession Used to calculate positions in the text
   * @return a range that starts one character after the end of the range parameter
   */
  public getRange(editSession: ace_types.Ace.EditSession) {
    const lastLine: number = editSession.getLine(this.end.getPosition().row)
      .length;
    if (this.end.getPosition().column === lastLine) {
      // The end of the range is at the end of a line
      return new Range(
        this.start.getPosition().row,
        this.start.getPosition().column,
        this.end.getPosition().row + 1,
        0
      );
    } else {
      // The end of the range is not at the end of a line
      return new Range(
        this.start.getPosition().row,
        this.start.getPosition().column,
        this.end.getPosition().row,
        this.end.getPosition().column + 1
      );
    }
  }

  /**
   * Setter for the range of the marker. Saves a range that ends one character before the given range parameter
   * @param range The range where the marker is set
   * @param editSession The session to anchor the ranges to, also used to calculate positions
   */
  public setRange(
    range: ace_types.Ace.Range,
    editSession: ace_types.Ace.EditSession
  ) {
    let row = range.end.row;
    let column;
    if (range.end.column === 0) {
      // The end of the range is at the start of a line
      column = editSession.getLine(range.end.row - 1).length;
      row = range.end.row - 1;
    } else {
      column = range.end.column - 1;
    }
    this.start = editSession
      .getDocument()
      .createAnchor(range.start.row, range.start.column);
    this.end = editSession.getDocument().createAnchor(row, column);
    this.start.detach();
    this.end.detach();
  }

  public onChange(delta: any) {
    this.start.onChange(delta);
    this.end.onChange(delta);
    if(delta.action === 'remove' && delta.start.column !== 0
        && delta.start.row === this.end.row && delta.start.column === this.end.column){
      this.end.column = this.end.column - 1;
      if(this.start.row === this.end.row && this.start.column === this.end.column){
        this.deleted = true;
      }
    }
  }
}

/**
 * Adds a new AnchoredMarker to an array of existing ones so that no overlaps occur.
 * Newer added markers will overwrite the old ones. That way you can sort the inputs by priority.
 * @param markers Array of existing markers
 * @param range Range of the marker to be added
 * @param message Message of the marker to be added
 * @param type Type of the marker to be added
 * @param editSession The editor Object, used in the AnchoredMarker constructor
 */
export function addToArray(
  markers: AnchoredMarker[],
  range: ace_types.Ace.Range,
  message: string,
  type: string,
  editSession: ace_types.Ace.EditSession
) {
  for (let i = 0; i < markers.length; i++) {
  const existingRange: ace_types.Ace.Range = markers[i].getRange(editSession);
    switch (existingRange.compareRange(range)) {
      case 1:
        // Existing range ends in the new range
        if (type === markers[i].type) {
          // The markers have the same type: combine into one.
          range.start = existingRange.start;
          markers.splice(i, 1);
          i--;
        } else {
          // Cut off the part of the marker that would overlap
          existingRange.end = range.start;
          markers[i].setRange(existingRange, editSession);
        }
        break;
      case 0:
        // One of the ranges contains the other
        if (existingRange.containsRange(range) && markers[i].type !== type) {
          const rangeBefore: ace_types.Ace.Range = Range.fromPoints(
            existingRange.start,
            range.start
          );
          markers[i].setRange(rangeBefore, editSession);
          existingRange.start = range.end;
          markers.push(
            new AnchoredMarker(
              existingRange,
              markers[i].message,
              markers[i].type,
              editSession
            )
          );
        } else {
          markers.splice(i, 1);
          i--;
        }
        break;
      case -1:
        // The new range ends in the existing range
        if (type === markers[i].type) {
          range.end = existingRange.end;
          markers.splice(i, 1);
          i--;
        } else {
          existingRange.start = range.end;
          markers[i].setRange(existingRange, editSession);
        }
        break;
      default:
        if (
          existingRange.isEnd(range.start.row, range.start.column) &&
          type === markers[i].type
        ) {
          range.start = existingRange.start;
          markers.splice(i, 1);
          i--;
        }
        if (
          existingRange.isStart(range.end.row, range.end.column) &&
          type === markers[i].type
        ) {
          range.end = existingRange.end;
          markers.splice(i, 1);
          i--;
        }
    }
  }
  markers.push(new AnchoredMarker(range, message, type, editSession));
  return markers;
}
