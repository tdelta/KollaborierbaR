import React from 'react';
import ReactDOM from 'react-dom';
import './index.css';

// Import Brace and the AceEditor Component
import brace from 'brace';
import AceEditor from 'react-ace';

// Import a Mode (language)
import 'brace/mode/java';

// Import a Theme (okadia, github, xcode etc)
import 'brace/theme/monokai';

class App extends React.Component {
    render() {
	return (
	<div id = "editor">
		<AceEditor	
			mode="java"
			theme="monokai"
			width="100%"
			height="100%"
			onChange={this.onChange}
			onLoad={(editor)=> {
				editor.setOptions({
				autoScrollEditorIntoView: true,
				copyWithEmptySelection: true,
				fontSize: 15,
				firstLineNumber: 1,
				});
			}}
		/>
	</div>
	);
    }
}

ReactDOM.render(
	<App />,
	document.getElementById('root')
);
