import React from 'react';

import PropTypes from 'prop-types';

/** 
 * Used to render symbols for files and folders.
 * ProjectTreeView depends on this component, to annotate folders and
 * files with symbols. (Uses FontAwesome symbols.)
 *
 * It does show different symbols for open and closed folders
 * and even different symbols depending on file extensions
 * (for now only markdown)
 *
 * Examples:
 *
 * ```jsx
 *     <FileIcon
 *         data={{
 *             'name': 'Test.java',
 *             'type': 'file'
 *         }}
 *     />
 *     <FileIcon
 *         data={{
 *             'name': 'src',
 *             'type': 'folder'
 *         }}
 *         isOpen={true}
 *     />
 * ```
 */
class FileIcon extends React.Component {
    /**
     * identifyExtension : String -> @Nullable String
     * 
     * Tries to extract a file extension from a file's name.
     * 
     * Examples:
     *
     * ```javascript
     *     identifyExtension('Test.java') === 'java'
     *     identifyExtension('Many.dots.hs') === 'hs'
     *     identifyExtension('.vimrc') === 'vimrc'
     *     identifyExtension('NoExtension') === null
     * ```
     */
    identifyExtension(name) {
        // we'll use regular expressions to extract the file extension

        // regular expression based on
        // https://stackoverflow.com/a/680982
        const re = /(?:(?:\.)([^.]+))?$/;
        const match = re.exec(name);

        // if the expression matched, return the capture group
        if (match && match.length > 1) {
            return match[1];
        }

        else {
            return null;
        }
    }

    render() {
        // if no specific icon can be determined, use a question mark as
        // default symbol
        var icon = 'question';

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
                }

                else {
                    icon = 'far fa-folder';
                }

                break;
        }

        // if parent set additional classes through the className property,
        // append them to the icon class
        var className = icon;
        if (this.props.className) {
            className += ' ' + this.props.className;
        }

        return (
            <i className={className} />
        );
    }
}

FileIcon.propTypes = {
    /** Additional classes set by parent */
    'className': PropTypes.string,

    /** Information about the file, this icon shall represent. */
    'data': PropTypes.shape({
        'name': PropTypes.string.isRequired,
        'type': PropTypes.oneOf(['file', 'folder']).isRequired
    }).isRequired,

    /**
     * Whether the symbol shall indicate, that the file/folder has been opened.
     * Currently only supported for folders.
     */
    'isOpen': PropTypes.bool
};

FileIcon.defaultProps = {
    'isOpen': false
};

export default FileIcon;
