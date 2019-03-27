import { Network } from '../network';
import KeYApi from '../key/KeYApi';

import ProofNode from '../key/prooftree/ProofNode';
import ObligationResult from '../key/netdata/ObligationResult';

import { serverAddress } from '../constants';

/**
 * Manages synchronization of proofs between clients working on the same file.
 *
 * For this, it subscribes to a
 * <a href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP destination</a>
 * at the backend server via a websocket.
 * This destination corresponds to the currently opened file and using the
 * destination, the backend sends us event messages, which inform about changes, like new proofs run by other clients.
 *
 * For more information, consult the backend documentation of class
 * synchronization.ProofSyncController.
 */
export default class ProofSyncController {
  private network: Network;
  private observer: ProofEventObserver;
  private currentProjectName?: string;
  private currentFilePath?: string[];
  private currentTopic?: string;

  /**
   * @param network - access to a websocket connection with the server, needed for synchronization between clients.
   * @param observer - this observer will be informed about changes to proofs, this controller witnesses.
   *                   Usually it is used to update the UI when a change happens.
   */
  constructor(network: Network, observer: ProofEventObserver) {
    this.network = network;
    this.observer = observer;

    this.setObligationResult = this.setObligationResult.bind(this);
    this.genTopic = this.genTopic.bind(this);
    this.openFile = this.openFile.bind(this);
    this.closeFile = this.closeFile.bind(this);
  }

  /**
   * Helper method for generating the correct STOMP destination/topic we need
   * to subscribe to, if we want the server to inform us about changes regarding
   * a specific file.
   */
  private genTopic(projectName: string, path: string[]): string {
    return `/user/projects/proof/${projectName}/${path.join('/')}`;
  }

  /**
   * Whenever a file is opened, the application should call this function.
   * It causes this controller to subscribe to the corresponding STOMP destination, see class description.
   *
   * After calling this function, the observer will be informed about updates to proofs regarding this file.
   * until {@link #closeFile} is called.
   */
  public openFile(projectName: string, path: string[]): Promise<void> {
    const topic = this.genTopic(projectName, path);

    return this.network
      .safeSubscribe(
        topic,
        msg => {
          try {
            const event: ProofEvent = JSON.parse(msg.body);

            console.log(`incoming proof event`, event);

            switch (event.eventType) {
              case ProofEventType.UpdatedProof:
                this.observer.onUpdatedProof(event);
                break;

              case ProofEventType.UpdatedProofHistory:
                this.observer.onUpdatedHistory(event);
                break;
            }
          } catch (e) {
            console.error('Failed to parse server event');
            console.error(e);
          }
        },
        {}
      )
      .then(() => {
        this.currentProjectName = projectName;
        this.currentFilePath = path;
        this.currentTopic = topic;
      });
  }

  /**
   * Whenever a file is closed, the application should call this function.
   * It causes this controller to unsubscribe from the corresponding STOMP destination, see class description.
   */
  public closeFile(): Promise<void> {
    if (this.currentTopic == null) {
      return Promise.reject(
        'There is no topic set, we can not close the current proof context'
      );
    } else {
      return this.network.safeUnsubscribe(this.currentTopic);
    }
  }

  /**
   * Sets the most recent proof result for the currently opened file / obligation at the
   * server, so that other clients may access it.
   */
  public setObligationResult(obligationResult: ObligationResult): void {
    if (
      this.currentTopic == null ||
      this.currentFilePath == null ||
      this.currentProjectName == null
    ) {
      console.error(
        'There is no topic set, we can not determine the current proof context'
      );
    } else {
      KeYApi.uploadLatestProof(
        this.currentProjectName,
        this.currentFilePath.join('/'),
        obligationResult
      );
    }
  }
}

export enum ProofEventType {
  /** someone editing the file ran a proof and changed the most recent proof result */
  UpdatedProof = 'UpdatedProofEvent',
  /** someone editing the file saved or deleted a proof result from the proof result history */
  UpdatedProofHistory = 'UpdatedProofHistoryEvent',
}

/**
 * The server informs the client about changes to proofs of the currently opened
 * file by sending {@link ProofSyncController} events, which indicate, what changed.
 *
 * Those events conform to this interface.
 */
export interface ProofEvent {
  eventType: ProofEventType;
  projectName: string;
  filePath: string;
  obligationIdx: number;
}

export interface UpdatedProofEvent extends ProofEvent {}
export interface UpdatedProofHistoryEvent extends ProofEvent {}

/**
 * Enables user of {@link ProofSyncController} to listen for changes to the
 * proofs regarding the currently opened project.
 * See contructor documentation of {@link ProofSyncController}.
 */
interface ProofEventObserver {
  onUpdatedProof(event: ProofEvent): void;

  onUpdatedHistory(event: ProofEvent): void;
}
