import React from 'react';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

class TreeNode extends React.Component {
    constructor(props) {
        super(props);

        this.state = {
            'visible': true
        }
    }

    renderIcon(data) {
        var icon = 'question';

        switch (data.type) {
            case 'file':
                icon = 'file';
                break;
            case 'folder':
                if (this.state.visible) {
                    icon = 'folder-open';
                }

                else {
                    icon = 'folder';
                }

                break;
        }

        return (
            <FontAwesome name={icon} className="projectTreeIcon" />
        );
    }

    toggle() {
        if (this.state.visible) {
            this.setState({
                'visible': false
            });
        }

        else {
            this.setState({
                'visible': true
            });
        }
    }

    handleItemDoubleClick() {
        if (this.props.data.type === 'file') {
            this.props.onOpenFile(this.props.path);
        }
    }

    render() {
        if (this.props.data.hasOwnProperty('contents')) {
            const visibility = {
                'display': this.state.visible ?
                    ''
                    : 'none'
            };

            return (
                <>
                    <div onClick={() => {this.toggle();}}>
                        {this.renderIcon(this.props.data)}
                        {this.props.data.name}
                    </div>
                    <ul
                        className="projectTreeList"
                        style={visibility}
                    >
                        {
                            this.props.data.contents.map((child) =>
                                <li key={child.name}>
                                    <TreeNode
                                        data={child}
                                        path={this.props.path.concat([child.name])}
                                        onOpenFile={this.props.onOpenFile}
                                    />
                                </li>
                            )
                        }
                    </ul>
                </>
            );
        }

        else {
            return (
                <div onDoubleClick={this.handleItemDoubleClick.bind(this)}>
                    {this.renderIcon(this.props.data)}
                    {this.props.data.name}
                </div>
            );
        }
    }
}

class ProjectTreeView extends React.Component {
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
                            <TreeNode
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

export default ProjectTreeView;
