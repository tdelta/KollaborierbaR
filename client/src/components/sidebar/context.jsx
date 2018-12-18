import React from 'react';
import {Collapse, ListGroup} from 'reactstrap';
import './sidebar.css';
import PropTypes from 'prop-types';


export default class Context extends React.Component{
    constructor(props) {
        super(props);
        this.node = null;
        this.handleRightClick = this.handleRightClick.bind(this);
        this.handleContextClick = this.handleContextClick.bind(this);
        this.closeContext = this.closeContext.bind(this);
        this.handleMouseDown = this.handleMouseDown.bind(this);

        this.state = {
            context: false,
        };
    }

    handleRightClick() {
        this.setState({ context: !this.state.context });
    }

    closeContext() {
        this.setState({ context: false });
    }

    render() {
        const childrenWithProps = React.Children.map(this.props.children, child =>
            //TODO: Fix warning
            child.type === ContextMenu ?
                React.cloneElement(
                    child,
                    {
                        context: this.state.context,
                    }
                )
                : child
        );

        return(
            <div onContextMenu={this.handleRightClick} ref={elem => this.node = elem}>
                {childrenWithProps}
            </div>
        );
    }

    handleContextClick(e) {
        e.preventDefault();
        if (this.node !== null && e.target !== this.node && !this.node.contains(e.target)) {
            this.closeContext();
        }
    }

    handleMouseDown(e) {
        // if its a left click, close the context menu.
        if (e.which === 1) {
            this.closeContext();
        }
    }

    componentDidMount() {
        // addeventlistener doesnt add handlers twice 
        document.addEventListener('contextmenu', this.handleContextClick);
        document.addEventListener('click', this.handleMouseDown);
    }

    componentWillUnmount() {
        // Make sure to remove the DOM listener when the component is unmounted.
        document.removeEventListener('contextmenu', this.handleContextClick);
        document.removeEventListener('click', this.handleMouseDown);
    }

}

Context.propTypes = {
    children: PropTypes.node
};

class ContextMenu extends React.Component{
    render() {
        return (
            <Collapse isOpen={this.props.context}>
                <ListGroup className='contextList'>
                    {this.props.children}
                </ListGroup>
            </Collapse>
        );
    }
}

ContextMenu.propTypes = {
    context: PropTypes.bool,
    children: PropTypes.node
};

export class ContextAction extends React.Component {
    render() {
        return <li className='contextAction' onClick={this.props.onClick}>{this.props.children}</li>;
    }
}


ContextAction.propTypes = {
    children: PropTypes.node,
    onClick: PropTypes.func,
};

export {Context, ContextMenu};

