import KeyApi from './key-api';
import ProofResults from './netdata/ProofResults';
import ObligationResult from './netdata/ObligationResult';
import NotificationSystem from 'react-notification-system';
import { RefObject } from 'react';

import OpenGoalInfo from './netdata/OpenGoalInfo';

export default class Key {
  private keyApi: KeyApi = new KeyApi();
  private getFilePath: () => string;
  private setProvenObligations: (provenObligations: number[]) => void;
  private notificationSystem: RefObject<NotificationSystem.System>;
  private setProofResults: (proofResults: ProofResults) => void;
  private setOpenGoals: (openGoals: OpenGoalInfo[]) => void;

  private addNewConsoleMessage: (message: String) => void;

  private contractRegex: RegExp = /normal_behaviour|exceptional_behaviour|normal_behavior|exceptional_behavior/g;
  // Find method declarations in the current line 
  // https://stackoverflow.com/questions/68633/regex-that-will-match-a-java-method-declarations
  private methodRegex: RegExp = /^[ \t]*(?:(?:public|protected|private)\s+)?(?:(static|final|native|synchronized|abstract|threadsafe|transient|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))\s+){0,}(?!return)\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})\s+\b\w+\b\s*\(\s*(?:\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*(?:,\s+\b([\w.]+)\b(?:|(?:<[?\w\[\] ,&]+>)|(?:<[^<]*<[?\w\[\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\w\[\] ,&]+>[^>]*>[^>]*>))((?:\[\]){0,})(\.\.\.)?\s+(\w+)\b(?![>\[])\s*){0,})?\s*\)(?:\s*throws [\w.]+(\s*,\s*[\w.]+))?\s*(?:\{|;)[ \t]*$/;
  constructor(
    notificationSystem: RefObject<NotificationSystem.System>,
    setProvenObligations: (provenObligations: number[]) => void,
    setProofResults: (proofResults: ProofResults) => void,
    setOpenGoals: (openGoals: OpenGoalInfo[]) => void,
    getFilePath: () => string,
    addNewConsoleMessage: (message: String) => void
  ) {
    this.notificationSystem = notificationSystem;
    this.setProvenObligations = setProvenObligations;
    this.getFilePath = getFilePath;
    this.proveFile = this.proveFile.bind(this);
    this.proveObligation = this.proveObligation.bind(this);
    this.isMethodDeclaration = this.isMethodDeclaration.bind(this);
    this.getObligations = this.getObligations.bind(this);
    this.getContractsForMethod = this.getContractsForMethod.bind(this);
    this.setProofResults = setProofResults;
    this.setOpenGoals = setOpenGoals;

    this.sendNotifications = this.sendNotifications.bind(this);
    this.handleResults = this.handleResults.bind(this);

    this.addNewConsoleMessage = addNewConsoleMessage;
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

  private sendNotifications(results: ProofResults): void {
    // print succeeded proofs as success notifications
    if (this.notificationSystem.current) {
      this.notificationSystem.current.clearNotifications();
      for (const success of results.succeeded) {
        this.notificationSystem.current.addNotification({
          title: 'Success!',
          message: success.resultMsg,
          level: 'success',
          position: 'bc',
          autoDismiss: 15,
        });
      }
      // print fails as warnings
      for (const fail of results.failed) {
        this.notificationSystem.current.addNotification({
          title: 'Failure!',
          message: fail.resultMsg,
          level: 'warning',
          position: 'bc',
          autoDismiss: 15,
        });
      }
      // print exception messages as errors
      for (const error of results.errors) {
        this.notificationSystem.current.addNotification({
          title: 'Error!',
          message: error.resultMsg,
          level: 'error',
          position: 'bc',
          autoDismiss: 15,
        });
      }

      for(const stackTrace of results.stackTraces){
        this.addNewConsoleMessage(stackTrace.resultMsg);
      }
    }
  }

  public proveObligation(nr: number) {
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
    const provenObligations: number[] = results.succeeded.map(
      success => success.obligationIdx
    );

    this.setProofResults(results);

    this.setProvenObligations(provenObligations);

    this.setOpenGoals(results.openGoals);

    this.sendNotifications(results);
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
        const obligations: RegExpMatchArray | null = lines[i].match(this.contractRegex);
        if (obligations) {
          numObligations += obligations.length;
          result[i] = numObligations - 1;
        }
      }
      return result;
    }

    public isMethodDeclaration(line: string): boolean {
      return this.methodRegex.test(line)
    }

    public getContractsForMethod(lines: string[], row: number): number[] {
      const result: number[] = [];
      if (this.isMethodDeclaration(lines[row])) {
        let numObligations = 0;
        for (let i = 0; i < lines.length; i += 1) {
          const obligations: RegExpMatchArray | null = lines[i].match(this.contractRegex);
          if (obligations) {
            numObligations += obligations.length;
            result.push(numObligations - 1);
          }
          if (row == i) {
              break;
          } else if (this.isMethodDeclaration(lines[i])) {
              result.length = 0;
            }
        }
      }
      return result;
    }
}
