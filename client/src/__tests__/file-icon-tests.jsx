import React from 'react';
import renderer from 'react-test-renderer';

import FileIcon from '../components/sidebar/file-icon.jsx';

test('file extension identification', () => {
    // build a file icon instance
    var file = {
        'name': '',
        'type': 'file'
    };

    const instance = renderer.create(
        <FileIcon data={file} />
    ).getInstance();

    // run some tests on its file extension identification ability
    const checkExtension = (filename, expectedExtension) => {
        expect(
            instance.identifyExtension(filename)
        ).toEqual(expectedExtension);
    };

    checkExtension('Test.java', 'java');
    checkExtension('README.md', 'md');
    checkExtension('.vimrc', 'vimrc');
    checkExtension('Many.dots.hs', 'hs');
    checkExtension('NoExtension', null);
});
