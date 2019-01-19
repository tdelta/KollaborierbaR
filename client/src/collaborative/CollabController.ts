import Editor from '../components/editor';

import TextPosition from './TextPosition';

import Network from './Network';
import {LogootSRopes, TextInsert, TextDelete, LogootSOperation, LogootSAdd, LogootSDel, Identifier} from 'mute-structs';
import {Range} from 'ace-builds';

export default class CollabController {
  private document!: LogootSRopes;
  private network: Network;
  private editor: any;
  private setText: (text: string) => void;
  private filename!: string;

  constructor(net: Network, editor: Editor,setText: (text: string) => void) {
    this.network = net;
    this.editor = editor.editor; // Ace editor
    this.setText = setText;

    this.editor.on('change',(delta: any) => {
    if (this.document && // We are connected to a collaborative document
    this.editor.curOp && this.editor.curOp.command.name) { // The edit came from the user
      const headers: any = {file: this.filename};
      const start: number = this.editor.session.doc.positionToIndex(delta.start);
      let operation: LogootSOperation;
        switch(delta.action){
          case 'insert':
            operation = this.document.insertLocal(start,delta.lines.join('\n'));
            this.network.broadcast('insert',headers,operation);
            console.log(this.document);
            break;
          case 'remove':
            const end: number = start + delta.lines.join(' ').length-1;
            operation = this.document.delLocal(start,end);
            this.network.broadcast('remove',headers,operation);
        }
      }
    });
  }

  public setFile(filename: string){
    this.filename = filename;
    // Unsubscribe from previous file
    //this.network.unsubscribe('insert');
    //this.network.unsubscribe('remove');
    //this.network.unsubscribe('crdt-doc');
    // Subscribe to new file
    const headers = {'file': filename};
    this.network.on([
    {messageType: 'insert',headers: headers,callback: this.handleRemoteInsert.bind(this)},
    {messageType: 'remove', headers: headers,callback: this.handleRemoteRemove.bind(this)},
    {messageType: 'crdt-doc',headers: headers,callback: this.handleDocumentInit.bind(this)}]);
  }

  public handleRemoteInsert(operation: any){
    operation = JSON.parse(operation);
    console.log(operation);
    const operationObj: LogootSAdd | null = LogootSAdd.fromPlain(operation);
    let deltas: TextInsert[] = [];
    if(operationObj != null) deltas = operationObj.execute(this.document);
    for(const delta of deltas){
      const position: TextPosition = this.editor.session.doc.indexToPosition(delta.index);
      this.editor.session.insert(position,delta.content);
    }
  }

  public handleRemoteRemove(operation: any){
    operation = JSON.parse(operation);
    const operationObj: LogootSDel | null = LogootSDel.fromPlain(operation);
    let deltas: TextDelete[] = [];
    if(operationObj != null) deltas = operationObj.execute(this.document);
    for(const delta of deltas){
      const start: TextPosition = this.editor.session.doc.indexToPosition(delta.index);
      const end: TextPosition = this.editor.session.doc.indexToPosition(delta.index+delta.length);
      this.editor.session.replace(Range.fromPoints(start,end),'');
    }
  }

  public handleDocumentInit(doc: any){
    doc = JSON.parse(doc);
    const docObj: LogootSRopes | null = LogootSRopes.fromPlain(doc.replicaNumber,doc.clock,
      {
        str: doc.text,
        root: doc.root
        });
    console.log(docObj);
    if(docObj != null){
      this.document = docObj;
    }
    if(doc.root == null) {
      const operation: LogootSAdd = this.document.insertLocal(0,this.editor.getValue());
      this.network.broadcast('insert',{file: this.filename},operation);
    }
  }
}
