import React from 'react';
import ReactDOM from 'react-dom';
import './index.css';

import App from './components/app.jsx';

// render the main component (app) in a div (`root`) inside index.html
ReactDOM.render(
    <App />,
    document.getElementById('root')
);
