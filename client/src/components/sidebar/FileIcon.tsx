import React from 'react';

import FileOrFolder from '../../FileOrFolder';

/**
 * Used to render symbols for files and folders.
 * {@link ProjectTreeView} depends on this component, to annotate folders and
 * files with symbols. (Uses FontAwesome symbols, {@see https://fontawesome.com/}.)
 *
 * It does show different symbols for open and closed folders
 * and even different symbols depending on file extensions
 * (for now only markdown is supported.)
 */
export default class FileIcon extends React.Component<Props, {}> {
  // by default, the icon will indicate, that the folder is not opened, if it
  // represents a folder
  public static defaultProps = {
    isOpen: false,
  };

  /**
   * Tries to extract a file extension from a file's name.
   *
   * Examples:
   *
   * ```typescript
   *     identifyExtension('Test.java') === 'java'
   *     identifyExtension('Many.dots.hs') === 'hs'
   *     identifyExtension('.vimrc') === 'vimrc'
   *     identifyExtension('NoExtension') === null
   * ```
   */
  private identifyExtension(name: string): string | null {
    // we'll use regular expressions to extract the file extension

    // regular expression based on
    // https://stackoverflow.com/a/680982
    const re = /(?:(?:\.)([^.]+))?$/;
    const match = re.exec(name);

    // if the expression matched, return the capture group
    if (match && match.length > 1 && match[1]) {
      return match[1];
    } else {
      return null;
    }
  }

  /**
   * React lifecycle rendering method.
   * {@link https://reactjs.org/docs/react-component.html#render}
   *
   * See constructor documentation for information on what is being rendered.
   */
  public render() {
    // if no specific icon can be determined, use a question mark as
    // default symbol
    let icon = 'fa question';

    // check, whether the file in question is actually a file or a folder
    switch (this.props.data.type) {
      case 'file':
        // use different symbols for some file types
        switch (this.identifyExtension(this.props.data.name)) {
          case 'md':
            icon = 'fab fa-markdown';
            break;
          default:
            icon = 'far fa-file';
        }

        break;
      case 'folder':
        // show symbol of an opened folder, if
        // isOpen is set in props
        if (this.props.isOpen) {
          icon = 'far fa-folder-open';
        } else {
          icon = 'far fa-folder';
        }

        break;

      default:
        icon = 'fa question';
        break;
    }

    // if parent set additional classes through the className property,
    // append them to the icon class
    let className = icon;
    if (this.props.className) {
      className = `${className} ${this.props.className}`;
    }

    return <i className={className} />;
  }
}

interface Props {
  /** Additional classes set by parent */
  className: string;
  /** Information about the file, this icon shall represent. */
  data: FileOrFolder;
  /**
   * Whether the symbol shall indicate, that the file/folder has been opened.
   * Currently only supported for folders.
   */
  isOpen?: boolean;
}
