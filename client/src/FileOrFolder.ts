export enum FileFolderEnum {
  file = 'file',
  folder = 'folder',
}

export default interface FileOrFolder {
  name: string;
  type: FileFolderEnum;
  contents?: FileOrFolder[];
}
