import React from 'react';
import PropTypes from 'prop-types';
import FontAwesome from 'react-fontawesome';

import '@fortawesome/fontawesome-free/css/all.min.css';

// Why did I have to include this and sidebar.jsx doesnt need to include
// sidebar.css
import './console.css';

export default class Sidebar extends React.Component {

    constructor(props){
        super(props);

        this.state = {
            // whether the sidebar is currently hidden, or not
            'collapsed': true
        }
    }

    /**
     * invert visibility of the sidebar by collapsing it, or
     * restoring it.
     */
    toggle() {
        this.setState({
            'collapsed': !this.state.collapsed,
            'textheight': 0,
            'textwidth': 0
        });

        // Resize the div containing the editor depending wheter the console
        // is collapsed or not
        if(this.state.collapsed){
            var editor = document.getElementById("editor");
            editor.style.height = "68%";
        } else{
            var editor = document.getElementById("editor");
            editor.style.height = "98%";
        }

        //this.setConsoleTextAreaToCorrectSize();

        // Make other components recalculate their width (Im looking at you ace)
        window.dispatchEvent(new Event('resize'));
    }

    componentDidMount(){
        console.log("HI");
        this.setState({
            'textheight': document.getElementById("console").offsetHeight,
            'textwidth' :  document.getElementById("console").offsetWidth,
        });
        let textarea = document.getElementById("consoletext");
        console.log(this.state.textheight);
        console.log(this.state.textwidth);
        textarea.style.height = this.state.textheight;
        textarea.style.width = this.state.textwidth;
        
    }
    
    render(){

        const genVisibilityString = (collapsed) => collapsed ?
        'none' : '';

        
        var consoleStyleModForRestore = {
        'display': genVisibilityString(!this.state.collapsed)
        };  

        var consoleStyleModForCollapse = {
            'display': genVisibilityString(this.state.collapsed)
        }; 

        return(
            <>
            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForRestore}
                onClick = {this.toggle.bind(this)}
                
            >
                <FontAwesome
                    name= "angle-up" 
                /> 
            </div>

            <div 
                className = "consoleRestoreHandle"
                style = {consoleStyleModForCollapse}
                onClick = {this.toggle.bind(this)}
                
            >
                <FontAwesome
                    name= "angle-down" 
                /> 
            </div>

            <div 
                id = "console"
                style = {consoleStyleModForCollapse}
            >
            
            <textarea 
                id="consoletext"
            ></textarea>
            </div>
            </>
        );
    }
}