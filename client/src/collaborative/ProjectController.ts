import { Network } from '../network';

export default class ProjectController {
  private network: Network;
  private observer: ProjectEventObserver;

  constructor(network: Network, observer: ProjectEventObserver) {
    this.network = network;
    this.observer = observer;
  }

  public openProject(projectName: string): Promise<void> {
    return this.network.safeSubscribe(
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

  public closeProject(projectName: string): Promise<void> {
    const topic = `/user/projects/${projectName}`;

    return this.network.safeUnsubscribe(topic);
  }
}

export interface User {
  firstName: string;
  lastName: string;
  crdtId: number;
}

export enum ProjectEventType {
  UpdatedProject = 'UpdatedProjectEvent',
  DeletedProject = 'DeletedProjectEvent',
  DeletedFile = 'DeletedFileEvent',
  RenamedFile = 'RenamedFileEvent',
  UpdatedFile = 'UpdatedFileEvent',
  UsersUpdated = 'UsersUpdatedEvent',
}

export interface ProjectEvent {
  eventType: ProjectEventType;
  projectName: string;
}

export interface ProjectFileEvent extends ProjectEvent {
  filePath: string;
}

export interface RenamedFileEvent extends ProjectEvent {
  originalPath: string;
  newPath: string;
}

export interface UsersUpdatedEvent extends ProjectEvent {
  users: User[];
}

interface ProjectEventObserver {
  onProjectEvent(
    event: ProjectEvent | ProjectFileEvent | RenamedFileEvent
  ): void;
}
