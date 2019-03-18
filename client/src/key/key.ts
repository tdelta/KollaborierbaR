import KeyApi from './key-api';
import ProofResults from './netdata/ProofResults';
import ObligationResult, {ObligationResultKind} from './netdata/ObligationResult';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import { serverAddress } from '../constants';

import {Network} from '../network';
import ProofsState from '../key/ProofsState';

import ProofCollabController, { ProofEvent } from '../collaborative/ProofCollabController';

export default class Key {
  private keyApi: KeyApi = new KeyApi();
  private proofController: ProofCollabController;

  private getFilePath: () => string;
  private setProvenObligations: (provenObligations: number[]) => void;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private getProofsState: () => ProofsState;
  private setProofsState: (proofsState: ProofsState) => void;

  private addNewConsoleMessage: (message: String) => void;

  constructor(
    network: Network,
    notificationSystem: RefObject<NotificationSystem.System>,
    setProvenObligations: (provenObligations: number[]) => void,
    getProofsState: () => ProofsState,
    setProofsState: (proofsState: ProofsState) => void,
    getFilePath: () => string,
    addNewConsoleMessage: (message: String) => void
  ) {
    this.notificationSystem = notificationSystem;
    this.setProvenObligations = setProvenObligations;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligation = this.proveObligation.bind(this);
    this.getProofsState = getProofsState;
    this.setProofsState = setProofsState;
    this.sendLastProofNotifications = this.sendLastProofNotifications.bind(this);
    this.sendHistoryUpdateNotification = this.sendHistoryUpdateNotification.bind(this);
    this.handleResults = this.handleResults.bind(this);
    this.addNewConsoleMessage = addNewConsoleMessage;
    this.refreshLastProof = this.refreshLastProof.bind(this);

    this.proofController = new ProofCollabController(network,
      {
        onUpdatedProof: (event: ProofEvent) => {
          console.log('Key: Proof event: ', event);

          this.refreshLastProof(event.projectName, event.filePath, event.obligationIdx);
        },
        onUpdatedHistory: (event: ProofEvent) => {
          console.log('Key: Proof history event: ', event);

          this.refreshProofHistory(event.projectName, event.filePath, event.obligationIdx);
        }
      }
    );
  }

  private refreshLastProof(projectName: string, filePath: string, obligationIdx: number): void {
    fetch(`${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/last`, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    })
      .then(response => response.json())
      .then(obligationResult => {
        console.log('Key: Obligation result: ', obligationResult);

        this.setProofsState(
          this
            .getProofsState()
            .updateLastResultByObligationIdx(
              obligationResult.obligationIdx,
              obligationResult
            )
        );

        this.setProvenObligations(this.getProofsState().getProvenObligationIdxs());
        this.sendLastProofNotifications(obligationResult);
      });
  }


  private refreshProofHistory(projectName: string, filePath: string, obligationIdx: number): void {
    fetch(`${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history`, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    })
      .then(response => response.json())
      .then((historyIdxs: number[]) => {
        console.log("Retrieved history idxs: ", historyIdxs);

        return Promise.all(
          historyIdxs
            .map(historyIdx =>
              fetch(`${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history/${historyIdx}`, {
                method: 'GET',
                mode: 'cors', // enable cross origin requests. Server must also allow this!
                headers: {
                  Accept: 'application/json', // we want a json object back
                  //'Content-Type': 'application/json', // we are sending a json object
                },
              })
                .then(response => response.json())
            )
        )
      })
      .then((savedResults: ObligationResult[]) => {
        console.log('Key: Saved obligations: ', savedResults);

        this.setProofsState(
          this
            .getProofsState()
            .updateSavedResultsByObligationIdx(
              obligationIdx,
              savedResults
            )
        );

        this.sendHistoryUpdateNotification();
      });
  }

  public setCurrentFile(projectName: string, filePath: string[]) {
    this.proofController.openFile(projectName, filePath);

    const filePathJoined = filePath.join('/');

    fetch(`${serverAddress}/proof/${projectName}/${filePathJoined}/obligation`, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    })
      .then(response => response.json())
      .then((obligationIdxs: number[]) => {
        console.log("Retrieved obligation idxs: ", obligationIdxs);

        for (const obligationIdx of obligationIdxs) {
          this.refreshLastProof(projectName, filePathJoined, obligationIdx);
          this.refreshProofHistory(projectName, filePathJoined, obligationIdx);
        }
      });
  }

  private proveFile() {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      this.notificationSystem.current.addNotification({
        title: 'Please Wait!',
        message: 'Proving obligations...',
        level: 'info',
        position: 'bc',
        autoDismiss: 0,
      });
    }

    this.keyApi.proveFile(this.getFilePath()).then(this.handleResults);
  }

  private sendLastProofNotifications(obligationResult: ObligationResult): void {
    // print succeeded proofs as success notifications
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();

      switch (obligationResult.kind) {
        case ObligationResultKind.success:
          this.notificationSystem.current.addNotification({
            title: 'Success!',
            message: obligationResult.resultMsg,
            level: 'success',
            position: 'bc',
            autoDismiss: 15,
          });
        break;

        case ObligationResultKind.error:
          this.notificationSystem.current.addNotification({
            title: 'Error!',
            message: obligationResult.resultMsg,
            level: 'error',
            position: 'bc',
            autoDismiss: 15,
          });
        break;

        case ObligationResultKind.failure:
          this.notificationSystem.current.addNotification({
            title: 'Failure!',
            message: obligationResult.resultMsg,
            level: 'warning',
            position: 'bc',
            autoDismiss: 15,
          });
        break;
      }

      //for(const stackTrace of results.stackTraces){
      //  this.addNewConsoleMessage(stackTrace.resultMsg);
      //}
    }
  }

  private sendHistoryUpdateNotification(): void {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();

      this.notificationSystem.current.addNotification({
        title: 'History',
        message: 'The proof history has been updated.',
        level: 'info',
        position: 'bc',
        autoDismiss: 15,
      });
    }
  }

  public proveObligation(nr: number): Promise<void> {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      this.notificationSystem.current.addNotification({
        title: 'Please Wait!',
        message: 'Running proof obligation...',
        level: 'info',
        position: 'bc',
        autoDismiss: 0,
      });
    }

    return this.keyApi
      .proveObligation(this.getFilePath(), nr)
      .then(this.handleResults);
  }

  private handleResults(results: ProofResults): void {
    results
      .succeeded
      .concat(results.errors)
      .concat(results.failed)
      .forEach(this.proofController.setObligationResult);
  }

  /**
   * Finds all lines that contain proof obligations and gives each obligation an index.
   * @param Lines of a text that contains JML specifications
   * @result An array where the index of a line that contains proof obligations
   *    is set to the index of the last obligations in the line. For the other lines it is undefined
   */
  public getObligations(lines: string[]): number[] {
    let numObligations = 0;
    const result: number[] = [];
    for (let i = 0; i < lines.length; i += 1) {
      // Find the start of all proof obligations in the current line
      const regex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
      const obligations: RegExpMatchArray | null = lines[i].match(regex);
      if (obligations) {
        numObligations += obligations.length;
        result[i] = numObligations - 1;
      }
    }
    return result;
  }
}
