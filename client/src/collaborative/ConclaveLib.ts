import {CRDT, VersionVector, Identifier, Char} from 'conclave-lib';

import TextPosition from './TextPosition';

interface CrdtPosition {
  line: number;
  ch: number;
};

/**
 * Replacement for Conclave internal controller class to make Conclave CRDT
 * data types usable and abstract from its inner workings.
 *
 * (Conclave is an open source collaborative editor)
 *
 * This class therefore contains partially modified code from Conclave
 * written by the conclave-team: https://github.com/conclave-team/conclave#readme
 *
 * Ideally this is to be replaced by a customized CRDT implementation for our
 * use case, however, for now we rely on Conclave.
 **/
export default class ConclaveLib {
  public siteId: string;
  public vector: any;
  private crdt: any;
  private deletionBuffer: any[];

  private broadcastInsertFun: (operation: any) => void;
  private broadcastDeleteFun: (operation: any) => void;
  private insertIntoTextFun: (character: string, position: TextPosition) => void;
  private deleteTextFun: (from: TextPosition, to: TextPosition) => void;

  constructor(
    siteId: string,
    broadcastInsertFun: (operation: any) => void,
    broadcastDeleteFun: (operation: any) => void,
    insertIntoTextFun: (character: string, position: TextPosition) => void,
    deleteTextFun: (from: TextPosition, to: TextPosition) => void
  ) {
    this.siteId = siteId;
    this.vector = new VersionVector(this.siteId);
    this.deletionBuffer = [];

    this.broadcastInsertFun = broadcastInsertFun;
    this.broadcastDeleteFun = broadcastDeleteFun;
    this.insertIntoTextFun = insertIntoTextFun;
    this.deleteTextFun = deleteTextFun;

    // needs to be initialized last, since it will access the version vector
    // and siteId
    this.crdt = new CRDT(this);
  }

  private toTextPosition(position: CrdtPosition): TextPosition {
    return {
      row: position.line,
      column: position.ch
    };
  }

  private toCrdtPosition(position: TextPosition): CrdtPosition {
    return {
      line: position.row,
      ch: position.column
    };
  }
  
  public broadcastInsertion(crdtChar: any) {
    const operation = {
      type: 'insert',
      char: crdtChar,
      version: this.vector.getLocalVersion()
    };

    this.broadcastInsertFun(operation);
  }

  public broadcastDeletion(crdtChar: any, version: any) {
    const operation = {
      type: 'delete',
      char: crdtChar,
      version: version
    };

    this.broadcastDeleteFun(operation);
  }

  public localInsertCharacter(character: string, position: TextPosition) {
    this.crdt.handleLocalInsert(
      character,
      this.toCrdtPosition(position)
    );
  }

  public localDelete(from: TextPosition, to: TextPosition) {
    this.crdt.handleLocalDelete(
      this.toCrdtPosition(from),
      this.toCrdtPosition(to)
    );
  }

  public remoteInsert(operation: any) {
    if (this.vector.hasBeenApplied(operation.version)) {
      return;
    }

    const char: any = operation.char;
    const identifiers: any[] = char.position.map((pos: any) => new Identifier(pos.digit, pos.siteId));
    const newChar: any = new Char(char.value, char.counter, char.siteId, identifiers);

    this.crdt.handleRemoteInsert(newChar);

    this.vector.update(operation.version);

    this.processDeletionBuffer();
  }

  public remoteDelete(operation: any) {
    if (this.vector.hasBeenApplied(operation.version)) {
      return;
    }

    if (this.hasInsertionBeenApplied(operation)) {
      const char: any = operation.char;
      const identifiers: any[] = char.position.map((pos: any) => new Identifier(pos.digit, pos.siteId));
      const newChar: any = new Char(char.value, char.counter, char.siteId, identifiers);

      this.crdt.handleRemoteDelete(newChar, operation.version.siteId);
    }

    else {
      this.deletionBuffer.push(operation);
    }
  }

  private processDeletionBuffer(): void {
    let i = 0;
    let deleteOperation;

    while (i < this.deletionBuffer.length) {
      deleteOperation = this.deletionBuffer[i];

      if (this.hasInsertionBeenApplied(deleteOperation)) {
        this.remoteDelete(deleteOperation);
        this.deletionBuffer.splice(i, 1);
      } else {
        i++;
      }
    }
  }

  private hasInsertionBeenApplied(operation: any): boolean {
    const charVersion = { siteId: operation.char.siteId, counter: operation.char.counter };
    return this.vector.hasBeenApplied(charVersion);
  }

  public insertIntoEditor(character: string, position: CrdtPosition, siteId: string) {
    this.insertIntoTextFun(character, this.toTextPosition(position));
  }

  public deleteFromEditor(val: string, pos: any, siteId: string) {
    this.deleteTextFun(
      this.toTextPosition(pos),
      val === '\n' ?
      {
        row: pos.line + 1,
        column: 0
      } :
      {
        row: pos.line,
        column: pos.ch + 1
      }
    );
  }
}
