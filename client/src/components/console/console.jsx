import React from 'react';
import FontAwesome from 'react-fontawesome';
import '@fortawesome/fontawesome-free/css/all.min.css';
import './console.css';
import PropTypes from 'prop-types';

/**
 * This renders the console of KollaborierbaR. The 
 * console is displayed depending on the consoleIsVisible
 * property handed down from app.jsx. 
 */
export default class Console extends React.Component {

    render(){

        // Helper to determine the visibilty of the console
        const genVisibilityString = (collapsed) => collapsed ?
        'none' : '';

        //Set visiblity for the console, the consoleRestoreDiv and the consoleCollapseDiv
        let consoleStyleModForRestore = {
        'display': genVisibilityString(this.props.consoleIsVisible)
        };  

        let consoleStyleModForCollapse = {
            'display': genVisibilityString(!this.props.consoleIsVisible)
        }; 

        return(
            <>
            {/*Div which onClicks restores the console*/}
            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForRestore}
                onClick = {this.props.invertConsoleVisibility}
                
            >
            <div className= "consoleLable">
            Log
            </div>
             
                <FontAwesome
                    name= "angle-up"
                    className="consoleRestoreHandleIcon"
                /> 
            </div>

            {/*Div which onClicks collapses the console*/}
            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForCollapse}
                onClick = {this.props.invertConsoleVisibility}
                
            >
            <div className= "consoleLable">
            Log
            </div>
                <FontAwesome
                    name= "angle-down" 
                    className="consoleRestoreHandleIcon"
                /> 
            </div>
            
            {/*Actual console div */}
            <div 
                id = "console"
                style = {consoleStyleModForCollapse}
            >
                {/* Console message will be rendert in this div */}
                <div id="consoletext">
                    {this.props.consolelog}
                </div>
            </div>
            </>
        );
    }
}

Console.propTypes = {
    consolelog : PropTypes.string,
    consoleIsVisible : PropTypes.bool,
    invertConsoleVisibility : PropTypes.func
}