import Editor from '../components/editor';

import { Network, UsersUpdatedEvent } from '../network';
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
import * as ace_types from 'ace-builds';

import { IMessage } from '@stomp/stompjs';

export default class CollabController {
  private document: LogootSRopes | null = null;
  private network: Network;
  private editor: any;
  private editorComponent: Editor;
  private setText: (text: string) => void;
  private filepath!: string;
  private project!: string;
  private names: string[];
  private connected: boolean;

  constructor(net: Network, editor: Editor, setText: (text: string) => void) {
    this.network = net;
    this.editorComponent = editor;
    this.editor = editor.editor; // Ace editor
    this.setText = setText;
    this.names = [];
    this.connected = false;

    this.network.on('insert', {}, this.handleRemoteInsert.bind(this));
    this.network.on('remove', {}, this.handleRemoteRemove.bind(this));
    this.network.on('crdt-doc', {}, this.handleDocumentInit.bind(this));

    /**
     * Called when the user modifies the content of the editor
     * ATTENTION: ignoreChanges has to be set manually, when the text is modified programatically
     * @param delta Information about what change occured
     */
    this.editor.on('change', (delta: ace_types.Ace.Delta) => {
      if (
        this.document != null && // We are connected to a collaborative document
        !this.editor.ignoreChanges && // The event came from the user
        this.connected // A file is opened
      ) {
        const headers: any = { file: `${this.project}/${this.filepath}` };
        const start: number = this.editor.session.doc.positionToIndex(
          delta.start
        );
        let operation: LogootSOperation;
        switch (delta.action) {
          case 'insert':
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
      }
    });
  }

  /**
   * Needs to be called, when the user opens a file, to notify the socket that we want to receive updates.
   * @param project the name of the opened project
   * @param filepath the path of the opened file, seperated by /
   * @param content the content of the opened file
   */
  public setFile(project: string, filepath: string, content: string) {
    this.network.unsubscribe(`projects/${this.project}`);
    this.network.on(
      `projects/${project}`,
      {},
      this.handleNewUserName.bind(this)
    );
    if (filepath === '') {
      this.connected = false;
    } else {
      const file = `${project}/${filepath}`;
      this.network.broadcast('/file', { file: file }, { content: content });
      this.connected = true;
    }

    this.filepath = filepath;
    this.project = project;
  }

  /**
   * Handles user name events from the websocket, when a user connects from a project, disconnects from a project
   * or opens a file. the events also contain the id of the users crdt document.
   * If the event belongs to the currently opened file, the names of the users will be mapped to their id.
   * @param event
   * @param event.body a string that defines a UsersUpdatedEvent, containing the new list of usernames.
   */
  private handleNewUserName(event: IMessage) {
    const parsedEvent: UsersUpdatedEvent = JSON.parse(event.body);
    if (
      event.headers.file &&
      event.headers.file === `${this.project}/${this.filepath}`
    ) {
      this.names = [];
      for (const user of parsedEvent.users) {
        let lastName = user.lastName;
        lastName = lastName.charAt(0).toUpperCase() + lastName.slice(1);
        this.names[user.crdtId] = `${user.firstName} ${lastName}`;
      }
    }
  }

  /**
   * Handles remote insert events from the websocket
   * @param event
   * @param event.body a string that defines a json object matching the structure of LogootSAdd.
   *              It also has to pass some logic checks by the mute-struct library (in fromPlain).
   *              Otherwise the event will be dismissed.
   */
  public handleRemoteInsert(event: IMessage) {
    if (this.document != null) {
      const parsedOperation = JSON.parse(event.body);
      const operationObj: LogootSAdd | null = LogootSAdd.fromPlain(
        parsedOperation
      );
      // The resulting operations from applying the remove operation on the crdt document
      // Will be used to modify the text in the editor
      let deltas: TextInsert[] = [];
      if (operationObj != null) deltas = operationObj.execute(this.document);
      for (const delta of deltas) {
        const start: ace_types.Ace.Point = this.editor.session.doc.indexToPosition(
          delta.index
        );
        // The variable ignoreChanges makes sure our on change listener does not process the insert
        // The undo group is used to update old operations properly but not let the user undo the remote insert
        this.editor.ignoreChanges = true;
        let remoteUndo = this.editor.session.$undoManager.startNewGroup();
        const end: ace_types.Ace.Point = this.editor.session.insert(
          start,
          delta.content
        );
        this.editor.session.$undoManager.markIgnored(remoteUndo);
        this.editor.ignoreChanges = false;
        const uid: number =
          parsedOperation.id.tuples[parsedOperation.id.tuples.length - 1]
            .replicaNumber;
        this.editorComponent.addBackMarker(
          start,
          end,
          uid % 10,
          this.names[uid]
        );
      }
    }
  }

  /**
   * Handles remote remove events from the websocket
   * @param event
   * @param event.body a string that defines a json object matching the structure of LogootSDel.
   *              It also has to pass some logic checks by the mute-struct library (in fromPlain).
   *              Otherwise the event will be dismissed.
   */
  public handleRemoteRemove(event: IMessage) {
    if (this.document != null) {
      const parsedOperation = JSON.parse(event.body);
      const operationObj: LogootSDel | null = LogootSDel.fromPlain(
        parsedOperation
      );
      // The resulting operations from applying the remove operation on the crdt document
      // Will be used to modify the text in the editor
      let deltas: TextDelete[] = [];
      if (operationObj != null) deltas = operationObj.execute(this.document);
      for (const delta of deltas) {
        const start: ace_types.Ace.Point = this.editor.session.doc.indexToPosition(
          delta.index
        );
        const end: ace_types.Ace.Point = this.editor.session.doc.indexToPosition(
          delta.index + delta.length
        );
        // The variable ignoreChanges makes sure our on change listener does not process the insert
        // The undo group is used to update old operations properly but not let the user undo the remote insert
        this.editor.ignoreChanges = true;
        let remoteUndo = this.editor.session.$undoManager.startNewGroup();
        this.editor.session.replace(Range.fromPoints(start, end), '');
        this.editor.session.$undoManager.markIgnored(remoteUndo);
        this.editor.ignoreChanges = false;
      }
    }
  }

  /**
   * Handles file events, that the websocket sends after we connect to a document.
   * @param event
   * @param event.body a string that defines a json object matching the structure of LogootSRopes. (crdt document)
   *              It also has to pass some logic checks by the mute-struct library (in fromPlain).
   *              Otherwise the event will be dismissed.
   */
  public handleDocumentInit(event: IMessage) {
    const parsedDoc = JSON.parse(event.body);
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
