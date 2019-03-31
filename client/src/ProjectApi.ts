import FileOrFolder, { FileFolderEnum } from './FileOrFolder';
import { serverAddress } from './constants';
import OpenFileData from './projectmanagement';
import Project from './Project';

export default class ProjectApi {
  /**
   * Fetches contents and metadata of a file asynchronously from the server via
   * HTTP request.
   *
   * @param {string} path: path to file that shall be opened.
   *     It shall contain a leading '/' and the first folder shall be the
   *     project name.
   *
   * @returns {Promise} promise which will resolve to said contents and metadata.
   *
   * @example
   * openFile('/My Project/README.md').then((response) =>
   *   console.log(response.fileName); // yields "README.md"
   *   console.log(response.fileText); // yields contents of the README.md file
   * });
   */
  public static openFile(path: string): Promise<OpenFileData> {
    const escapedPath = escape(path);
    // API URL of the server we will use for our request
    const url = `${serverAddress}/projects/${escapedPath}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
        //'Content-Type': 'application/json', // we are sending a json object
      },
    }).then(response => {
      if (response.status === 200) {
        console.log('Parsing open file response: ', response);

        return response.json();
      } else {
        console.error('Opening file failed.', response);
      }
    });
  }

  /**
   * Load the list of available projects from the server.
   * @returns {Promise} which will resolve to a list of project names
   */
  public static getProjects(): Promise<string[]> {
    const url = `${serverAddress}/projects`;
    return fetch(url, {
      method: 'GET',
      mode: 'cors',
      headers: {
        Accept: 'application/json',
      },
    }).then(response => response.json());
  }

  /**
   * Calls the REST delete method.
   * TODO: Better explanation, what this method does
   * @param path - the path of the file to delete, relative to the projects folder on the server
   * @returns {Promise} which will resolve to updated project structure or empty when project got deleted
   */
  public static deleteOverall(path: string): Promise<Project | {}> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/projects/${escapedPath}`;

    return fetch(url, {
      method: 'DELETE',
      mode: 'cors', // enable cross origin requests. Server must also allow this!
      headers: {
        Accept: 'application/json', // we want a json object back
      },
    })
      .then(response => response.json()) // parse the response body as json
      .catch(() => undefined); // if the json body is empty (e.g. after project delete) return an empty json object
  }

  /**
   * Create file/folder/project on the server. Files have type == file.
   * Projects/folders have type == folder.
   * @param path - the path to the file to create
   * @returns {Promise} which will resolve to updated project structure
   */
  public static createOverall(
    path: string,
    type: FileFolderEnum
  ): Promise<Project> {
    const escapedPath = escape(path);

    const url = `${serverAddress}/projects/${escapedPath}?type=${type}`;
    return fetch(url, {
      method: 'PUT',
      mode: 'cors',
    }).then(response => response.json());
  }

  /**
   * That function makes a call to the HTTP rest controller
   * and updates the content of the file specified by the
   * parameters.
   * @param name - name of the affected project
   * @param path - path to the file that will be updated
   * @param content - content that will be set to the file
   */
  public static updateFileContent(
    name: string,
    path: string[],
    content: string
  ): Promise<Response> {
    // Path to the ressource we want to save
    // TODO: Check if project exists
    const url = `${serverAddress}/projects/${name}/${path.join('/')}`;

    const requestbody = {
      fileContent: content,
    };

    return fetch(url, {
      method: 'POST',
      mode: 'cors',
      headers: {
        Accept: 'application/json',
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestbody), // necessary if you want to send a JSON object in a fetch request
    }).then(response => response);
  }

  /**
   * Load a project from the server.
   * @param name - the name of the project
   * @returns {Promise} which resolves to the project
   */
  public static openProject(name: string): Promise<Project> {
    // Path to the ressource we want to rename
    // TODO: Handle if project not set
    const escapedName = escape(name);
    const url = `${serverAddress}/projects/${escapedName}`;

    return fetch(url, {
      method: 'GET',
      mode: 'cors',
    }).then(response => response.json());
  }

  /**
   * This function updates the filename of the given resource path.
   * @param projectName - the name of the afected project
   * @param path - the path to the file that should be renamed relative to the project
   * @param newName - the new name of the project
   * @return {Promise} which resolve to the updated project
   */
  public static updateFileName(
    projectName: string,
    path: string[],
    newName: string
  ): Promise<Project> {
    const url = `${serverAddress}/projects/${projectName}/${path.join('/')}`;
    const requestbody = {
      fileName: newName,
    };

    return fetch(url, {
      method: 'POST',
      mode: 'cors',
      headers: {
        Accept: 'application/json',
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestbody), // necessary if you want to send a JSON object in a fetch request
    }).then(response => response.json());
  }

  /**
   * Create a file inside a project.
   * @param path - the path to the file relative to the projects folder on the server
   * @param type - the type of the file that should be created (e.g. folder or file)
   * @return {Promise} which resolves to the structure of the created file
   */
  public static createFile(
    path: string,
    type: FileFolderEnum
  ): Promise<FileOrFolder> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/projects/${escapedPath}?type=${type}`;

    return fetch(url, {
      method: 'PUT',
      mode: 'cors',
    }).then(response => response.json());
  }

  /**
   * Update the contents of a file on the server.
   * @param path - the path to the file
   * @param contents - the content that should be in the file
   * @return {Promise} which resolves to the structure of the file
   *
   */
  public static updateFileContents(
    path: string,
    contents: string
  ): Promise<FileOrFolder> {
    const escapedPath = escape(path);
    const url = `${serverAddress}/projects/${escapedPath}`;

    return fetch(url, {
      method: 'POST',
      mode: 'cors',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ fileContent: contents }),
    }).then(response => response.json());
  }
}
