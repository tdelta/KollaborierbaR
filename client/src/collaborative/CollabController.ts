import Editor from '../components/editor';

import TextPosition from './TextPosition';

import UUID from 'uuid';

import Network from './Network';
import ConclaveLib from './ConclaveLib';

export default class CollabController {
  private crdt: any;
  private siteId: string;
  private versionVector: any;
  private conclaveLib: ConclaveLib;

  constructor(net: Network, editor: Editor) {
    this.siteId = UUID();

    this.conclaveLib = new ConclaveLib(
      this.siteId,
      net.broadcastOperation.bind(net),
      net.broadcastOperation.bind(net),
      editor.insert.bind(editor),
      editor.delete.bind(editor)
    );

    net.on('operation', this.handleRemoteOperation.bind(this));
  }

  public localInsertLines(lines: string[], position: TextPosition): void {
    let currentPosition: TextPosition = {
      row: position.row,
      column: position.column
    };

    let count = 0;
    for (let line of lines) {
      for (let character of line) {
        this.conclaveLib.localInsertCharacter(character, currentPosition);

        ++currentPosition.column;
      }

      if (count < lines.length - 1) {
        this.conclaveLib.localInsertCharacter('\n', currentPosition);
      }

      ++currentPosition.row;
      ++count;
      currentPosition.column = 0;
    }
  }

  public localDelete(from: TextPosition, to: TextPosition) {
    this.conclaveLib.localDelete(from, to);
  }

  private handleRemoteOperation(opstr: string): void {
    const op = JSON.parse(opstr);

    switch (op.type) {
      case 'insert':
        this.conclaveLib.remoteInsert(op);
        break;

      case 'delete':
        this.conclaveLib.remoteDelete(op);
        break;
    }
  }
}
