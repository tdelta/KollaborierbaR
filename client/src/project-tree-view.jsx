import React from 'react';

import PropTypes from 'prop-types';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import FileNode from './file-node.jsx';

export default class ProjectTreeView extends React.Component {
    render() {
        if (this.props.project.hasOwnProperty('contents')) {
            return (
                <>
                    <FontAwesome
                        name='cube'
                        className="projectTreeIcon"
                    /> {this.props.project.name}

                    <hr />

                    {
                        this.props.project.contents.map((item) =>
                            <FileNode
                                key={item.name}
                                data={item}
                                path={[item.name]}
                                onOpenFile={this.props.onOpenFile}
                            />
                        )
                    }
                </>
            );
        }

        else {
            return (<></>);
        }
    }
}

ProjectTreeView.propTypes = {
    'onOpenFile': PropTypes.func,
    'project': PropTypes.shape({
        'contents': PropTypes.arrayOf(
            PropTypes.instanceOf(FileNode)
        ).isRequired,
        'name': PropTypes.string.isRequired
    }).isRequired
};

ProjectTreeView.defaultProps = {
    'onOpenFile': () => {}
};
        
