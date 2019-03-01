import fc from 'fast-check';
import { Range, EditSession } from 'ace-builds';
import * as ace_types from 'ace-builds';

import AnchoredMarker, { addToArray } from '../components/AnchoredMarker';

const textLength: number = 100;
const numRanges: number = 10;

test('No range from the inputs gets left empty in the result and no ranges overlap', () => {
  fc.assert(
    // List of ranges to be interpreted as [startcol,startrow,endcol,endrow]
    fc.property(
      fc.array(fc.array(fc.integer(0, 100), 4, 4), 1, 10),
      (rangesInit: number[][]) => {
        let ranges: ace_types.Ace.Range[] = createRanges(rangesInit);
        let lines: string[] = createText(rangesInit);

        // Create an ace editSession with a text that can acommodate all of the ranges
        const editSession: any = new EditSession('', null);
        editSession.doc.insertMergedLines({ row: 0, column: 0 }, lines);

        // Execute the function to be tested
        let anchoredMarkers: anchoredMarker[] = [];
        for (const range of ranges) {
          anchoredMarkers = addToArray(
            anchoredMarkers,
            range,
            'test',
            'test',
            editSession
          );
        }

        // For every given range, assert that every position in it is inside exactly one marker
        for (const range of rangesInit) {
          for (let y: number = range[0]; y < range[2]; y++) {
            let x: number;
            if (y === range[0]) x = range[1];
            else x = 0;
            for (; x < lines[y].length; x++) {
              expect(
                numContainingMarkers(
                  { row: y, column: x },
                  anchoredMarkers,
                  editSession
                )
              ).toBeLessThanOrEqual(2);
            }
          }
          let x: number = 0;
          for (; x < range[3]; x++) {
            expect(
              numContainingMarkers(
                { row: range[2], column: x },
                anchoredMarkers,
                editSession
              )
            ).toBeLessThanOrEqual(2);
          }
        }
      }
    )
  );
});

const numContainingMarkers = function(
  position: ace_types.Ace.Position,
  anchoredMarkers: AnchoredMarker[],
  editSession: ace_types.Ace.EditSession
) {
  let containedIn: number = 0;
  for (const marker of anchoredMarkers) {
    if (marker.getRange(editSession).contains(position)) containedIn++;
  }
  if (containedIn > 1) console.log(position);
  return containedIn;
};

const createRanges = function(rangesInit: number[][]) {
  let ranges: ace_types.Ace.Range = [];
  // Create an array of valid ace range objects
  for (const range of rangesInit) {
    if (range[0] < range[2] || (range[0] == range[2] && range[1] < range[3])) {
      // The first position is before the second one
      ranges.push(new Range(range[0], range[1], range[2], range[3]));
    } else {
      ranges.push(new Range(range[2], range[3], range[0], range[1]));
    }
  }
  return ranges;
};

const createText = function(rangesInit: number[][]) {
  let lines: string[] = [];
  // Create a text that contains all ranges
  for (const range of rangesInit) {
    for (let i: number = 0; i <= range[0]; i++) {
      if (!lines[i]) lines[i] = '';
    }
    for (let i: number = 0; i <= range[2]; i++) {
      if (!lines[i]) lines[i] = '';
    }
    if (lines[range[0]].length < range[1])
      lines[range[0]] = Array(range[1]).join(' ');
    if (lines[range[2]].length < range[3])
      lines[range[2]] = Array(range[3]).join(' ');
  }
  return lines;
};
