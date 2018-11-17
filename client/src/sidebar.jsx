import React from 'react';

import PropTypes from 'prop-types';

class Sidebar extends React.Component {
    constructor(props) {
        super(props);

        this.sideBar = React.createRef();
        this.mainContent = React.createRef();
        this.state = {
            'sidebarWidth': 200
        };
    }

    moveSplitBar(e) {
        e.preventDefault();

        const movementHandler = (e) => {
            e.preventDefault();

            const minWidth = 100;
            const maxWidth = 400;

            const newWidth = e.pageX - this.sideBar.current.getBoundingClientRect().left;

            if (newWidth > minWidth && newWidth < maxWidth && e.pageX < window.innerWidth) {  
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
        var sidebarStyleMod = {
            'width': this.state.sidebarWidth
        };

        var mainStyleMod = {
            'marginLeft': this.state.sidebarWidth
        };
        
        return(
            <>
                <div className="sidebar" ref={this.sideBar} style={sidebarStyleMod}>
                    <div className="sidebar-split-bar" onMouseDown={this.moveSplitBar.bind(this)}>
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
