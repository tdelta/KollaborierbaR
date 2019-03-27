import { StompService } from '../StompService';

/**
 * Manages synchronization of the project tree with other clients working on
 * the same project.
 *
 * For this, it subscribes to a
 * <a href="https://stomp.github.io/stomp-specification-1.2.html#SUBSCRIBE">STOMP destination</a>
 * at the backend via a websocket.
 * This destination corresponds to the currently opened project and using the
 * destination, the backend sends us event messages, which inform about changes.
 *
 * For more information, consult the backend documentation of class
 * synchronization.ProjectSyncController.
 */
export default class ProjectSyncController {
  private stompService: StompService;
  private observer: ProjectEventObserver;

  /**
   * @param stompService - access to a websocket connection with the server, needed for synchronization between clients.
   * @param observer - this observer will be informed about changes to the project, this controller witnesses.
   *                   Usually it is used to update the UI when a change happens.
   */
  constructor(stompService: StompService, observer: ProjectEventObserver) {
    this.stompService = stompService;
    this.observer = observer;
  }

  /**
   * Whenever a project is opened, the application should call this function.
   * It causes this controller to subscribe to the corresponding STOMP destination, see class description.
   *
   * After calling this function, the observer will be informed about updates to the project structure,
   * until {@link #closeProject} is called.
   */
  public openProject(projectName: string): Promise<void> {
    return this.stompService.safeSubscribe(
      `/user/projects/${projectName}`,
      msg => {
        try {
          const event:
            | ProjectEvent
            | ProjectFileEvent
            | RenamedFileEvent
            | UsersUpdatedEvent = JSON.parse(msg.body);

          console.log(`incoming event`);
          console.log(event);

          this.observer.onProjectEvent(event);
        } catch (e) {
          console.error('Failed to parse server event');
          console.error(e);
        }
      },
      {}
    );
  }

  /**
   * Whenever a project is closed, the application should call this function.
   * It causes this controller to unsubscribe from the corresponding STOMP destination, see class description.
   */
  public closeProject(projectName: string): Promise<void> {
    const topic = `/user/projects/${projectName}`;

    return this.stompService.safeUnsubscribe(topic);
  }
}

export enum ProjectEventType {
  /** indicates, something about the project structure changed, for example that a file / folder has been created */
  UpdatedProject = 'UpdatedProjectEvent',
  /** indicates, that a project got deleted */
  DeletedProject = 'DeletedProjectEvent',
  /** indicates, that a file/folder got deleted */
  DeletedFile = 'DeletedFileEvent',
  /** indicates, that a file/folder got renamed */
  RenamedFile = 'RenamedFileEvent',
  /** indicates, that the content of a file changed */
  UpdatedFile = 'UpdatedFileEvent',
  /** the list of users working on the project changed */
  UsersUpdated = 'UsersUpdatedEvent',
}

/**
 * The server informs the client about changes to the structure of the currently opened project
 * by sending {@link ProjectSyncController} events, which indicate, what changed.
 *
 * Those events conform to this interface.
 */
export interface ProjectEvent {
  eventType: ProjectEventType;
  projectName: string;
}

/** All events with file related event types use this interface. */
export interface ProjectFileEvent extends ProjectEvent {
  filePath: string;
}

export interface RenamedFileEvent extends ProjectEvent {
  originalPath: string;
  newPath: string;
}

/**
 * The server also manages a list of users per project.
 * This list is accessible via {@link UsersUpdatedEvent} and the data conforms
 * to this interface.
 */
export interface User {
  firstName: string;
  lastName: string;
  /** unique id relative to the currently opened file */
  crdtId: number;
}

export interface UsersUpdatedEvent extends ProjectEvent {
  users: User[];
}

/**
 * Enables user of {@link ProjectSyncController} to listen for changes to the
 * currently opened project.
 * See contructor documentation of {@link ProjectSyncController}.
 */
interface ProjectEventObserver {
  onProjectEvent(
    event: ProjectEvent | ProjectFileEvent | RenamedFileEvent
  ): void;
}
