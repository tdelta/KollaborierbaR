import FileOrFolder from './FileOrFolder';

export default interface Project {
  name: string;
  contents: FileOrFolder[];
}
