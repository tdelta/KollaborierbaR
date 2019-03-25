export enum FileFolderEnum {
  file = 'file',
  folder = 'folder',
}

export default interface FileOrFolder {
  name: string;
  type: FileFolderEnum;
  contents?: FileOrFolder[];
}

/**
 * Sorts a list of files and folders by the following strategy:
 *
 * - folders will always be sorted before files
 * - other than that, the files and folders will be sorted by their name
 * - the sorting is case insensitive
 *
 * The original array will not be modified.
 */
export function sort(toBeSorted: FileOrFolder[]): FileOrFolder[] {
  const folder: FileOrFolder[] = [];
  const files: FileOrFolder[] = [];

  // first, create a flat copy of the original array and also divide the items into
  // separate arrays, based on whether they are files or folders.
  for (const f of toBeSorted) {
    if (f.type === 'folder') {
      folder.push(f);
    }

    if (f.type === 'file') {
      files.push(f);
    }
  }

  // case insensitive, comparison function following lexicographic order
  const lowerCaseSorter = (a: FileOrFolder, b: FileOrFolder) => {
    if (a.name.toLowerCase() < b.name.toLowerCase()) {
      return -1;
    }

    if (a.name.toLowerCase() > b.name.toLowerCase()) {
      return 1;
    }

    return 0;
  };

  folder.sort(lowerCaseSorter);
  files.sort(lowerCaseSorter);

  return folder.concat(files);
}
