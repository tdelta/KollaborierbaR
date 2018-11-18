import React from 'react';

import PropTypes from 'prop-types';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import ProjectTreeView from './project-tree-view.jsx';

class Sidebar extends React.Component {
    constructor(props) {
        super(props);

        this.sideBar = React.createRef();
        this.mainContent = React.createRef();

        this.minWidth = 100;
        this.maxWidth = 400;

        this.state = {
            'sidebarWidth': 200,
            'visible': true
        };
    }

    toggle() {
        this.setState({
            'visible': !this.state.visible
        });
    }

    moveSplitBar(e) {
        e.preventDefault();

        const movementHandler = (e) => {
            e.preventDefault();


            const newWidth = e.pageX - this.sideBar.current.getBoundingClientRect().left;

            if (newWidth > this.minWidth && newWidth < this.maxWidth && e.pageX < window.innerWidth) {  
                this.setState({
                    'sidebarWidth': newWidth
                });
            }
        };

        document.addEventListener(
            'mousemove',
            movementHandler
        );

        const mouseupHandler = (e) => {
            document.removeEventListener('mousemove', movementHandler);
            document.removeEventListener('mouseup', mouseupHandler);
        };

        document.addEventListener(
            'mouseup',
            mouseupHandler
        );
    }

    render() {
        const genVisibilityString = (visible) => visible ?
            '' : 'none';

        var sidebarStyleMod = {
            'width': this.state.sidebarWidth,
            'display': genVisibilityString(this.state.visible)
        };

        var restoreHandleStyleMod = {
            'display': genVisibilityString(!this.state.visible)
        };

        var mainStyleMod = {
            'marginLeft': this.state.visible ?
                this.state.sidebarWidth
                : 10
        };

        return(
            <>
                <div
                    className="sidebarRestoreHandle"
                    style={restoreHandleStyleMod}
                    onClick={this.toggle.bind(this)}
                >
                    <FontAwesome
                        className="sidebarRestoreButton"
                        name="angle-right"
                    />
                </div>
                <div className="sidebar" ref={this.sideBar} style={sidebarStyleMod}>
                    <div className="sidebar-split-bar" onMouseDown={this.moveSplitBar.bind(this)}>
                    </div>

                    <div
                        className="sidebarToggleButton"
                        onClick={this.toggle.bind(this)}
                    >
                        <FontAwesome name="chevron-circle-left" />
                    </div>

                    <div className="sidebarContent">
                        <div id="projectTree">
                            <ProjectTreeView
                                onOpenFile={(p) => {alert(p.join('/'));}}
                                onNewFile={(p) => {alert(p.join('/'));}}
                                onNewFolder={(p) => {alert(p.join('/'));}}

                                project={this.props.project}
                            />
                        </div>
                    </div>
                </div>
                <div className="sidebarMainContainer" ref={this.mainContent} style={mainStyleMod}>
                    {this.props.children}
                </div>
            </>
        );
    }
}

Sidebar.propTypes = {
    'children': PropTypes.element.isRequired
};

export default Sidebar;
