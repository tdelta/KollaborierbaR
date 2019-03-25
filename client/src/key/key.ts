import KeyApi from './key-api';
import ProofResults from './netdata/ProofResults';
import ObligationResult, {
  ObligationResultKind,
} from './netdata/ObligationResult';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import { serverAddress } from '../constants';

import { Network } from '../network';
import ProofsState from '../key/ProofsState';

import ProofCollabController, {
  ProofEvent,
} from '../collaborative/ProofCollabController';

export default class Key {
  private keyApi: KeyApi = new KeyApi();
  private proofController: ProofCollabController;

  private getFilePath: () => string;
  private setProvenObligations: (provenObligations: number[]) => void;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private getProofsState: () => ProofsState;
  private setProofsState: (proofsState: ProofsState) => void;
  private setObligationIdOfLastUpdatedProof: (obligationId: number) => void;

  private addNewConsoleMessage: (message: string) => void;

  private contractRegex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
  // Regex that matches method declarations
  // https://stackoverflow.com/questions/68633/regex-that-will-match-a-java-method-declarations
  private methodRegex: RegExp = /^[ \t]*(?:(?:public|protected|private)\s+)?(?:(\/\*.*\*\/|static|final|native|synchronized|abstract|threadsafe|transient|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))\s+){0,}(?!return)\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})\s+\b\w+\b\s*\(\s*(?:\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*(?:,\s+\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*){0,})?\s*\)(?:\s*throws [\w.]+(\s*,\s*[\w.]+))?\s*(?:\{|;)[ \t]*(\/\/.*)?$/;

  constructor(
    network: Network,
    notificationSystem: RefObject<NotificationSystem.System>,
    setProvenObligations: (provenObligations: number[]) => void,
    getProofsState: () => ProofsState,
    setProofsState: (proofsState: ProofsState) => void,
    setObligationIdOfLastUpdatedProof: (obligationId: number) => void,
    getFilePath: () => string,
    addNewConsoleMessage: (message: string) => void
  ) {
    this.notificationSystem = notificationSystem;
    this.setProvenObligations = setProvenObligations;
    this.setObligationIdOfLastUpdatedProof = setObligationIdOfLastUpdatedProof;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligations = this.proveObligations.bind(this);
    this.getProofsState = getProofsState;
    this.setProofsState = setProofsState;
    this.sendLastProofNotifications = this.sendLastProofNotifications.bind(
      this
    );
    this.sendHistoryUpdateNotification = this.sendHistoryUpdateNotification.bind(
      this
    );
    this.isMethodDeclaration = this.isMethodDeclaration.bind(this);
    this.getObligations = this.getObligations.bind(this);
    this.getContractsForMethod = this.getContractsForMethod.bind(this);
    this.handleResults = this.handleResults.bind(this);
    this.addNewConsoleMessage = addNewConsoleMessage;
    this.refreshLastProof = this.refreshLastProof.bind(this);
    this.saveObligationResult = this.saveObligationResult.bind(this);

    this.proofController = new ProofCollabController(network, {
      onUpdatedProof: (event: ProofEvent) => {
        console.log('Key: Proof event: ', event);

        this.refreshLastProof(
          event.projectName,
          event.filePath,
          event.obligationIdx
        );
      },
      onUpdatedHistory: (event: ProofEvent) => {
        console.log('Key: Proof history event: ', event);

        this.refreshProofHistory(
          event.projectName,
          event.filePath,
          event.obligationIdx
        );
      },
    });
  }

  private refreshLastProof(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): void {
    fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/last`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    )
      .then(response => response.json())
      .then(obligationResult => {
        console.log('Key: Obligation result: ', obligationResult);

        this.setProofsState(
          this.getProofsState().updateLastResultByObligationIdx(
            obligationResult.obligationIdx,
            obligationResult
          )
        );

        this.setProvenObligations(
          this.getProofsState().getProvenObligationIdxs()
        );
        this.sendLastProofNotifications(obligationResult);
        this.setObligationIdOfLastUpdatedProof(obligationResult.obligationIdx);
      });
  }

  private refreshProofHistory(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): void {
    fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    )
      .then(response => response.json())
      .then((historyIdxs: number[]) => {
        console.log('Retrieved history idxs: ', historyIdxs);

        return Promise.all(
          historyIdxs.map(historyIdx =>
            fetch(
              `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history/${historyIdx}`,
              {
                method: 'GET',
                mode: 'cors', // enable cross origin requests. Server must also allow this!
                headers: {
                  Accept: 'application/json', // we want a json object back
                  //'Content-Type': 'application/json', // we are sending a json object
                },
              }
            ).then(response => response.json())
          )
        );
      })
      .then((savedResults: ObligationResult[]) => {
        console.log('Key: Saved obligations: ', savedResults);

        this.setProofsState(
          this.getProofsState().updateSavedResultsByObligationIdx(
            obligationIdx,
            savedResults
          )
        );

        this.sendHistoryUpdateNotification();
      });
  }

  public saveObligationResult(
    projectName: string,
    filePath: string,
    obligationResult: ObligationResult
  ): void {
    console.log('Trying to save an obligation result: ', obligationResult);

    fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${
        obligationResult.obligationIdx
      }/history`,
      {
        method: 'POST',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(obligationResult), // necessary if you want to send a JSON object in a fetch request
      }
    ).then(response => {
      if (response.status !== 200) {
        alert('Uups! Failed to save obligation.');
      } else {
        console.log('Saved obligation result to server');
      }
    });
  }

  public deleteObligationResult(
    projectName: string,
    filePath: string,
    obligationIdx: number,
    historyIdx: number
  ): void {
    console.log(
      'Trying to delete an element from history at index ',
      historyIdx
    );

    fetch(
      `${serverAddress}/proof/${projectName}/${filePath}/obligation/${obligationIdx}/history/${historyIdx}`,
      {
        method: 'DELETE',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
      }
    ).then(response => {
      if (response.status !== 200) {
        alert('Uups! Failed to delete element from history.');
      } else {
        console.log('Successfully deleted element from history.');
      }
    });
  }

  public setCurrentFile(projectName: string, filePath: string[]) {
    this.proofController.openFile(projectName, filePath);

    const filePathJoined = filePath.join('/');

    fetch(
      `${serverAddress}/proof/${projectName}/${filePathJoined}/obligation`,
      {
        method: 'GET',
        mode: 'cors', // enable cross origin requests. Server must also allow this!
        headers: {
          Accept: 'application/json', // we want a json object back
          //'Content-Type': 'application/json', // we are sending a json object
        },
      }
    )
      .then(response => response.json())
      .then((obligationIdxs: number[]) => {
        console.log('Retrieved obligation idxs: ', obligationIdxs);

        for (const obligationIdx of obligationIdxs) {
          this.refreshLastProof(projectName, filePathJoined, obligationIdx);
          this.refreshProofHistory(projectName, filePathJoined, obligationIdx);
        }
      });
  }

  /**
   * Tries to prove all obigations in the current file and displays a status
   * notification that a proof is in progress
   */
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

  /**
   * Initiates the proving of obliagtions and displays a neat notification
   *
   * @param nr - the index or indices of obligations that should be proved
   * @returns a pending promise for the prove, whose value is undefined when
   * it gets fullfiled
   */
  public proveObligations(nr: number | number[]) {
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      this.notificationSystem.current.addNotification({
        title: 'Please Wait!',
        message:
          typeof nr === 'number'
            ? 'Proving obligation...'
            : 'Proving obligations...',
        level: 'info',
        position: 'bc',
        autoDismiss: 0,
      });
    }

    return this.keyApi
      .proveObligations(this.getFilePath(), nr)
      .then(this.handleResults);
  }

  private handleResults(results: ProofResults): void {
    results.succeeded
      .concat(results.errors)
      .concat(results.failed)
      .forEach(this.proofController.setObligationResult);
  }

  /**
   * Finds all lines that contain proof obligations and gives each obligation an index.
   * @param lines - Lines of a text that contains JML specifications
   * @returns An array where the index of a line that contains proof obligations
   * is set to the index of the last obligations in the line. For the other lines it is undefined
   */
  public getObligations(lines: string[]): number[] {
    let numObligations = 0;
    const result: number[] = [];
    for (let i = 0; i < lines.length; i += 1) {
      // Find the start of all proof obligations in the current line
      const obligations: RegExpMatchArray | null = lines[i].match(
        this.contractRegex
      );
      if (obligations) {
        numObligations += obligations.length;
        result[i] = numObligations - 1;
      }
    }
    return result;
  }

  /**
   * Checks if a string is a valid method declaration by matching it against
   * a regular expression
   * @param line - the string that should be tested
   * @returns a boolean which is true when the input is method declaration and
   * false when not
   */
  public isMethodDeclaration(line: string): boolean {
    return this.methodRegex.test(line);
  }

  /**
   * Returns the indices of the proof obligations that belong to certain method
   * @param lines - a string array which is filled with the string lines of a file
   * @param row - the line number which contains the potential method declaration
   * @returns a list which contains the indices of proofobligations, if the row
   * parameter is the line number of a method declaration and the method has
   * proof obligations
   */
  public getContractsForMethod(lines: string[], row: number): number[] {
    const result: number[] = [];

    if (this.isMethodDeclaration(lines[row])) {
      let numObligations = 0;

      for (let i = 0; i < lines.length; i += 1) {
        const obligations: RegExpMatchArray | null = lines[i].match(
          this.contractRegex
        );

        if (obligations) {
          numObligations += obligations.length;
          result.push(numObligations - 1);
        }

        if (row === i) {
          break;
        } else if (this.isMethodDeclaration(lines[i])) {
          result.length = 0;
        }
      }
    }
    return result;
  }
}
