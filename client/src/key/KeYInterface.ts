import KeYApi from './KeYApi';
import ProofResults from './netdata/ProofResults';
import ObligationResult, {
  ObligationResultKind,
} from './netdata/ObligationResult';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import { serverAddress } from '../constants';

import { Network } from '../network';
import ProofsState from '../key/ProofsState';

import ProofSyncController, {
  ProofEvent,
} from '../collaborative/ProofSyncController';

/**
 * Provides access to features of the
 * <a href="https://key-project.org">KeY project</a>
 * for the client application and other useful proof related services.
 *
 * For many of those functions it employs the KollaborierbaR backend server.
 *
 * Provided services include:
 *
 * - proving specifications of Java methods
 * - storing a history of proof results
 * - synchonizing proof results between clients working on the same file
 */
export default class KeYInterface {
  /** synchronization service for proof results between clients */
  private proofController: ProofSyncController;

  // various callbacks allowing to manipulate application UI on proof result related events
  // or for retrieving information from the application.
  // See constructor for a description of them

  private getFilePath: () => string;
  private setProvenObligations: (provenObligations: number[]) => void;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private getProofsState: () => ProofsState;
  private setProofsState: (proofsState: ProofsState) => void;
  private setObligationIdOfLastUpdatedProof: (obligationId: number) => void;
  private addNewConsoleMessage: (message: string) => void;

  /** currently selected macro */
  private macro: string = '';

  /** Regex that matches JML behaviour declarations */
  private contractRegex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
  /**
   * Regex that matches method declarations
   * https://stackoverflow.com/questions/68633/regex-that-will-match-a-java-method-declarations
   */
  private methodRegex: RegExp = /^[ \t]*(?:(?:public|protected|private)\s+)?(?:(\/\*.*\*\/|static|final|native|synchronized|abstract|threadsafe|transient|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))\s+){0,}(?!return)\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})\s+\b\w+\b\s*\(\s*(?:\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*(?:,\s+\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*){0,})?\s*\)(?:\s*throws [\w.]+(\s*,\s*[\w.]+))?\s*(?:\{|;)[ \t]*(\/\/.*)?$/;

  /**
   * This interface needs to be provided various callbacks to be able to
   * integrate backend services into the application.
   *
   * @param network - access to a websocket connection with the server, needed for synchronization between clients.
   * @param notificationSystem - allows to send notifications to the UI, which will directly be displayed to the user. Useful to inform about changes caused by other clients working on the same file.
   * @param setProvenObligations - allows to set the list of proven obligations, so that the UI may display which proofs have been closed
   * @param getProofsState - retrieves the state of available proofs displayed in the UI
   * @param setProofsState - change the state of available proof results displayed in the UI
   * @param setObligationIdOfLastUpdatedProof - inform the UI about an proof obligation whose proof results recently changed
   * @param getFilePath - allows to retrieve the currently opened file
   * @param addNewConsoleMessage - display a message in the console at the bottom of the UI
   */
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
    this.setMacro = this.setMacro.bind(this);

    // Initialize the proof synchronization service.
    // It must be supplied callbacks, which are invoked, if the proof state
    // is changed for all clients of the current file.
    // (Happens for example, when we or someone else working on the file saves a proof to history)
    this.proofController = new ProofSyncController(network, {
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

  /**
   * Sets the proof script to be used for all following proofs
   *
   * @param macro - path to the proof script
   */
  public setMacro(macro: string) {
    this.macro = macro;
  }

  /**
   * Refresh the UI with the most recent proof result for a file / obligation.
   * This method is usually called, whenever {@link ProofSyncController}
   * indicates, that it changed (for example if another client tried to prove
   * the obligation)
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the latest proof
   *                        shall be retrieved.
   */
  private refreshLastProof(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): void {
    KeYApi.downloadLatestProof(projectName, filePath, obligationIdx).then(
      obligationResult => {
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
      }
    );
  }

  /**
   * Refresh the UI with the most recent proof result history for a file / obligation.
   * This method is usually called, whenever {@link ProofSyncController}
   * indicates, that it changed (for example if another client saved a proof
   * to the history, or deleted one).
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which the latest proof
   *                        shall be retrieved.
   */
  private refreshProofHistory(
    projectName: string,
    filePath: string,
    obligationIdx: number
  ): void {
    KeYApi.downloadAllHistoricProofs(projectName, filePath, obligationIdx).then(
      (savedResults: ObligationResult[]) => {
        console.log('Key: Saved obligations: ', savedResults);

        this.setProofsState(
          this.getProofsState().updateSavedResultsByObligationIdx(
            obligationIdx,
            savedResults
          )
        );

        this.sendHistoryUpdateNotification();
      }
    );
  }

  /**
   * Sets the most recent proof for a specific file / obligation on the server,
   * so that it can be shared with other clients working on the same file.
   */
  public saveObligationResult(
    projectName: string,
    filePath: string,
    obligationResult: ObligationResult
  ): void {
    console.log('Trying to save an obligation result: ', obligationResult);

    KeYApi.saveHistoricProof(projectName, filePath, obligationResult);
  }

  /**
   * Deletes a proof result from the server's history for a
   * specific file / obligation
   *
   * @param obligationIdx - index of the obligation (counted from top to bottom
   *                        in the source file), for which a result shall be
   *                        deleted
   * @param historyIdx - which result shall be deleted from the history?
   *                     {@link #downloadHistoryIds) can be used to retrieve a
   *                     list of ids available on the server.
   */
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

    KeYApi.deleteHistoricProof(
      projectName,
      filePath,
      obligationIdx,
      historyIdx
    );
  }

  /**
   * Downloads saved proofs from the backend server history and updates the UI
   * for the specified file.
   * Also instructs the synchronization service {@link ProofSyncController}
   * to synchronize proofs with other clients for this file.
   *
   * This method should be called by the application for everytime a file is
   * opened.
   */
  public setCurrentFile(projectName: string, filePath: string[]) {
    this.proofController.openFile(projectName, filePath);

    const filePathJoined = filePath.join('/');

    KeYApi.downloadObligationIds(projectName, filePathJoined).then(
      (obligationIdxs: number[]) => {
        console.log('Retrieved obligation idxs: ', obligationIdxs);

        for (const obligationIdx of obligationIdxs) {
          this.refreshLastProof(projectName, filePathJoined, obligationIdx);
          this.refreshProofHistory(projectName, filePathJoined, obligationIdx);
        }
      }
    );
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

    KeYApi.proveFile(this.getFilePath(), this.macro).then(this.handleResults);
  }

  /**
   * Internal helper method, which is used to inform the user about changes to
   * the most recent proof via notifications.
   */
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

  /**
   * Internal helper method, which is used to inform the user about changes to
   * the most proof history via notifications.
   */
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

    return KeYApi.proveObligations(this.getFilePath(), nr, this.macro).then(
      this.handleResults
    );
  }

  /**
   * Called, whenever a proof request to the backend server finishes.
   * It informs the synchronization service {@link ProofSyncController}
   * about the results, which in turn informs the server, which informs other
   * clients (and ourselves) to download the updated proof state.
   */
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
