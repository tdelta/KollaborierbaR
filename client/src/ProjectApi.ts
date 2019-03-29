import FileOrFolder, { FileFolderEnum } from './FileOrFolder';
import { serverAddress } from './constants';

export default class ProjectApi {
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
