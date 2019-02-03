import Editor from '../components/editor';

import TextPosition from './TextPosition';

import { Network } from '../network';
import {
  LogootSRopes,
  TextInsert,
  TextDelete,
  LogootSOperation,
  LogootSAdd,
  LogootSDel,
  Identifier,
} from 'mute-structs';
import { Range } from 'ace-builds';

export default class CollabController {
  private document: LogootSRopes | null = null;
  private network: Network;
  private editor: any;
  private editorComponent: Editor;
  private setText: (text: string) => void;
  private filename!: string;
  private uidBase: number;

  constructor(net: Network, editor: Editor, setText: (text: string) => void) {
    this.network = net;
    this.editorComponent = editor;
    this.editor = editor.editor; // Ace editor
    this.setText = setText;

    // this.uidBase = Math.floor(Math.random() * 10);
    this.uidBase = 0;

    this.network.on('insert', {}, this.handleRemoteInsert.bind(this));
    this.network.on('remove', {}, this.handleRemoteRemove.bind(this));
    this.network.on('crdt-doc', {}, this.handleDocumentInit.bind(this));

    this.editor.on('change', (delta: any) => {
      if (
        this.document != null && // We are connected to a collaborative document
        !this.editor.ignoreChanges
      ) {
        // The event came from the user
        const headers: any = { file: this.filename };
        const start: number = this.editor.session.doc.positionToIndex(
          delta.start
        );
        let operation: LogootSOperation;
        switch (delta.action) {
          case 'insert':
            console.log(delta.lines);
            operation = this.document.insertLocal(
              start,
              delta.lines.join('\n')
            );
            this.network.broadcast('/insert', headers, operation);
            break;
          case 'remove':
            const end: number = start + delta.lines.join(' ').length - 1;
            operation = this.document.delLocal(start, end);
            this.network.broadcast('/remove', headers, operation);
        }
        this.editor.curOp = undefined;
        console.log(this.document.str);
      }
    });
  }

  public setFile(filename: string, content: string) {
    this.filename = filename;
    this.network.broadcast('/file', { file: filename }, { content: content });
  }

  public handleRemoteInsert(operation: any) {
    if (this.document != null) {
      const parsedOperation = JSON.parse(operation);
      const operationObj: LogootSAdd | null = LogootSAdd.fromPlain(
        parsedOperation
      );

      let deltas: TextInsert[] = [];
      if (operationObj != null) deltas = operationObj.execute(this.document);
      for (const delta of deltas) {
        const start: TextPosition = this.editor.session.doc.indexToPosition(
          delta.index
        );
        this.editor.ignoreChanges = true;
        const end: TextPosition = this.editor.session.insert(
          start,
          delta.content
        );
        this.editor.ignoreChanges = false;
        const uid: number =
          (parsedOperation.id.tuples[parsedOperation.id.tuples.length - 1]
            .replicaNumber +
            this.uidBase) %
          10;
        this.editorComponent.addBackMarker(start, end, uid);
      }
      console.log(this.document.str);
    }
  }

  public handleRemoteRemove(operation: any) {
    if (this.document != null) {
      const parsedOperation = JSON.parse(operation);
      const operationObj: LogootSDel | null = LogootSDel.fromPlain(
        parsedOperation
      );
      let deltas: TextDelete[] = [];
      if (operationObj != null) deltas = operationObj.execute(this.document);
      for (const delta of deltas) {
        const start: TextPosition = this.editor.session.doc.indexToPosition(
          delta.index
        );
        const end: TextPosition = this.editor.session.doc.indexToPosition(
          delta.index + delta.length
        );
        this.editor.ignoreChanges = true;
        this.editor.session.replace(Range.fromPoints(start, end), '');
        this.editor.ignoreChanges = false;
      }
      console.log(this.document.str);
    }
  }

  public handleDocumentInit(doc: any) {
    const parsedDoc = JSON.parse(doc);
    // Try to parse the json into a LogootSRopes (crdt document) object.
    // If this fails, the document variable will remain null and inputs to the editor will be dismissed
    const docObj: LogootSRopes | null = LogootSRopes.fromPlain(
      parsedDoc.replicaNumber,
      parsedDoc.clock,
      {
        str: parsedDoc.text,
        root: parsedDoc.root,
      }
    );
    if (docObj != null) {
      this.document = docObj;
      // Replace the content of the editor with the current collaborative state of the file
      this.setText(this.document.str);
    }
  }
}
