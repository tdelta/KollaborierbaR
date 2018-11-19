import React from 'react';

import PropTypes from 'prop-types';

import '@fortawesome/fontawesome-free/css/all.min.css';
import FontAwesome from 'react-fontawesome';

import ProjectTreeView from './project-tree-view.jsx';

/**
 * Allows to display a project view in a window left from the main content
 * (usually an editor).
 *
 * It's length is variable and can be changed by the user.
 * It can also be hidden and restored by clicking a button.
 *
 * The project structure has to be supplied using a `project` JSON property.
 * See ProjectTreeView for more details on it.
 *
 * An `onOpenFile` handler can also be passed as property. It will be called
 * whenever a file within the project structure is double clicked by the
 * user. It will be passed the path to said file within the project.
 * For more details, see ProjectTreeView.
 *
 * The main content has to be supplied as the body of this component.
 *
 * Example:
 * 
 * ```jsx
 *     <Sidebar
 *         project={{
 *             'name': 'My Project',
 *             'contents': [
 *                 {
 *                     'name': 'src',
 *                     'type': 'folder',
 *                     'contents': [
 *                         {'name': 'Test.java', 'type': 'file'}
 *                     ]
 *                 },
 *                 {'name': 'README.md', 'type': 'file'}
 *              ]
 *         }}
 *         onOpenFile={(path) => console.log(path)}
 *      >
 *          <b>I am the main content!</b>
 *      </Sidebar>
 * ```
 */
export default class Sidebar extends React.Component {
    constructor(props) {
        super(props);

        // handles to rendered sub components
        this.sideBar = React.createRef();
        this.mainContent = React.createRef();

        // Minimum and maximum width of this sidebar.
        // These settings determine, how much the user can control its size.
        this.minWidth = 100;
        this.maxWidth = 400;

        // determine, whether the initial project property is set and
        // contains anything. If not, the sidebar will be collapsed initially.
        const isProjectValid =
               this.props.project // the project property is set to something
            && Object.keys(this.props.project).length !== 0;
            // ^ the project object must not be empty

        this.state = {
            // current width of the sidebar
            'sidebarWidth': 200,
            // whether the sidebar is currently hidden, or not
            'collapsed': isProjectValid ? 
                // only display the sidebar initially, if a project is set
                false
                : true
        };
    }

    /**
     * invert visibility of the sidebar by collapsing it, or
     * restoring it.
     */
    toggle() {
        this.setState({
            'collapsed': !this.state.collapsed
        });
    }

    /**
     * Handles resizing the sidebar when user holds the left mouse button
     * down on the bar, that splits sidebar and main content.
     */
    moveSplitBar(e) {
        // whatever usually happens, when pressing the mouse down on the split
        // bar (bar that splits view into sidebar and main content), suppress
        // it.
        e.preventDefault();

        // this function will translate mouse movement into adaptions to
        // the sidebar's width.
        const movementHandler = (e) => {
            // same effect as above
            e.preventDefault();

            // we want to the splitbar to be whereever the user is currently
            // moving the mouse.
            //
            // Therefore, the new width of the sidebar is calculated,
            // by subtracting the sidebars current offset to the left window
            // border from the x coordinate of the mouse.
            const newWidth = e.pageX - this.sideBar.current.getBoundingClientRect().left;

            // check, that the new width does not violate the minimum and
            // maximum width restrictions. Also check, that the mouse is still
            // within the window.
            if (newWidth > this.minWidth && newWidth < this.maxWidth && e.pageX < window.innerWidth) {  
                this.setState({
                    'sidebarWidth': newWidth
                });
            }
        };

        // the user pressed down on the split bar.
        // Until they let go, the above handler shall process mouse movement
        document.addEventListener(
            'mousemove',
            movementHandler
        );

        // remove the installed handlers, as soon as the user lets go of
        // the split bar (stops pressing the left button)
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
        // Visibility of split bar components will be controlled by
        // employing the css display property.
        // This function helps to calculate appropriate values for it.
        const genVisibilityString = (collapsed) => collapsed ?
            'none' : '';

        // css manipulation of sidebar components, depending on the
        // current width and visibility
        var sidebarStyleMod = {
            'width': this.state.sidebarWidth,
            'display': genVisibilityString(this.state.collapsed)
        };

        var restoreHandleStyleMod = {
            'display': genVisibilityString(!this.state.collapsed)
        };

        // if the sidebar is collapsed, keep a small margin from the left
        // regarding the main content, such that the restoration button is 
        // visible.
        //
        // If it is not collapsed, the left margin must be as wide as the
        // sidebar.
        var mainStyleMod = {
            'marginLeft': this.state.collapsed ?
                10
                : this.state.sidebarWidth
        };

        return(
            <>
                {/* this bar will be used to restore the sidebar,
                    if it has been collapsed. */}
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
                    {/* this bar will be used to resize the sidebar */}
                    <div className="sidebar-split-bar" onMouseDown={this.moveSplitBar.bind(this)}>
                    </div>

                    {/* pressing this button shall collapse the sidebar */}
                    <div
                        className="sidebarToggleButton"
                        onClick={this.toggle.bind(this)}
                    >
                        <FontAwesome name="chevron-circle-left" />
                    </div>

                    <div className="sidebarContent">
                        <div id="projectTree">
                            <ProjectTreeView
                                onOpenFile={this.props.onOpenFile}
                                onNewFile={(p) => {alert(p.join('/'));}}
                                onNewFolder={(p) => {alert(p.join('/'));}}

                                project={this.props.project}
                            />
                        </div>
                    </div>
                </div>

                {/* main content. The sidebar will be displayed left from it. */}
                <div className="sidebarMainContainer" ref={this.mainContent} style={mainStyleMod}>
                    {this.props.children}
                </div>
            </>
        );
    }
}

Sidebar.propTypes = {
    'children': PropTypes.element.isRequired,
    'project': PropTypes.shape({
        'name': PropTypes.string.isRequired,
        'contents': PropTypes.arrayOf(PropTypes.object)
    }),
    'onOpenFile': PropTypes.func
};