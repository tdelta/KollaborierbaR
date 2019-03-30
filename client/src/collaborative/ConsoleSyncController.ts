import { StompService } from '../StompService';

/**
 * Handles the connection to the websocket to receive console messages
 * for the file that is currently opened
 */
export default class ConsoleSyncController {
  private stompService: StompService;
  private currentProjectName?: string;
  private currentFilePath?: string[];
  private currentTopic?: string;
  private consoleObserver: ConsoleEventObserver;
  private errorObserver: ErrorEventObserver;

  /**
   * @param stompService - access to a websocket connection with the server, needed for synchronization between clients.
   * @param consoleObserver - this observer will be informed about changes to the console, this controller witnesses.
   * @param errorObserver - this observer will be informed about incoming error messages that this controller witnesses.
   */
  constructor(
    stompService: StompService,
    consoleObserver: ConsoleEventObserver,
    errorObserver: ErrorEventObserver
  ) {
    this.stompService = stompService;
    this.consoleObserver = consoleObserver;
    this.errorObserver = errorObserver;

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
    return `/user/console/${projectName}/${path.join('/')}`;
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

    let maybeUnsubscribe: Promise<void>;
    if (this.currentTopic != null) {
      maybeUnsubscribe = this.closeFile();
    } else {
      maybeUnsubscribe = Promise.resolve();
    }

    return maybeUnsubscribe
      .then(() =>
        this.stompService.safeSubscribe(
          topic,
          msg => {
            console.log(msg);
            const consoleEvent: ConsoleEvent = JSON.parse(msg.body);
            switch (consoleEvent.eventType) {
              case ConsoleEventType.Error:
                this.errorObserver.onErrorEvent(consoleEvent as ErrorEvent);
                break;
              case ConsoleEventType.ConsoleMessage:
                this.consoleObserver.onConsoleEvent(
                  consoleEvent as ConsoleMessageEvent
                );
                break;
            }
          },
          {}
        )
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
      return this.stompService.safeUnsubscribe(this.currentTopic).then(() => {
        this.currentTopic = undefined;
        this.currentFilePath = undefined;
        this.currentProjectName = undefined;
      });
    }
  }
}

// Enum used to differentiate types of websocket messages
enum ConsoleEventType {
  Error = 'ErrorEvent',
  ConsoleMessage = 'ConsoleMessageEvent',
}

// Base type for all events this controller will receive
export interface ConsoleEvent {
  eventType: ConsoleEventType;
  projectName: string;
  filePath: string;
  message: string;
}

// Events containing messages for the console
export interface ConsoleMessageEvent extends ConsoleEvent {}
// Events containing error messages
export interface ErrorEvent extends ConsoleEvent {}

// Observers can implement this interface to register for console events
export interface ConsoleEventObserver {
  onConsoleEvent(msg: ConsoleMessageEvent): void;
}

// Observers can implement this interface to register for error events
export interface ErrorEventObserver {
  onErrorEvent(msg: ErrorEvent): void;
}
