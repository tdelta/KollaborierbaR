import React from 'react';
import PropTypes from 'prop-types';
import FontAwesome from 'react-fontawesome';

import '@fortawesome/fontawesome-free/css/all.min.css';

// Why did I have to include this and sidebar.jsx doesnt need to include
// sidebar.css
import './console.css';

export default class Sidebar extends React.Component {

    render(){

        const genVisibilityString = (collapsed) => collapsed ?
        'none' : '';

        let consoleStyleModForRestore = {
        'display': genVisibilityString(this.props.consoleIsVisible)
        };  

        let consoleStyleModForCollapse = {
            'display': genVisibilityString(!this.props.consoleIsVisible)
        }; 

        return(
            <>
            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForRestore}
                onClick = {this.props.invertConsoleVisibility}
                
            >
                <FontAwesome
                    name= "angle-up"
                    className="consoleRestoreHandleIcon"
                /> 
            </div>

            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForCollapse}
                onClick = {this.props.invertConsoleVisibility}
                
            >
                <FontAwesome
                    name= "angle-down" 
                    className="consoleRestoreHandleIcon"
                /> 
            </div>

            <div 
                id = "console"
                style = {consoleStyleModForCollapse}
            >
                <div id="consoletext">
                    {this.props.consolelog}
                </div>
            </div>
            </>
        );
    }
}