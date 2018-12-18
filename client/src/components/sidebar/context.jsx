import React from 'react';
import {Collapse, ListGroup} from 'reactstrap';
import './sidebar.css';
import PropTypes from 'prop-types';


export default class Context extends React.Component{
    constructor(props) {
        super(props);
        this.node = null;
        this.handleRightClick = this.handleRightClick.bind(this);
        this.handleContextClose = this.handleContextClose.bind(this);
        this.closeContext = this.closeContext.bind(this);

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
                        closeContext: this.closeContext
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

    handleContextClose(e) {
        e.preventDefault();
        if (e.target !== this.node && !this.node.contains(e.target)) {
            this.setState({ context: false });
        }
    }

    componentDidUpdate() {
        if (this.props.tree() != null)
            // addeventlistener doesnt add handlers twice 
            this.props.tree().addEventListener('contextmenu', this.handleContextClose);
    }

    componentWillUnmount() {
        if (this.props.tree() != null)
        // Make sure to remove the DOM listener when the component is unmounted.
            this.props.tree().removeEventListener('contextmenu', this.handleContextClose);
    }

}

Context.propTypes = {
    tree: PropTypes.func,
    children: PropTypes.node
};


class ContextMenu extends React.Component{
    constructor(props) {
        super(props);
    }

    render() {
        const childrenWithProps = React.Children.map(this.props.children, child => {
            //TODO: Fix warning
            if (child.type === ContextAction) {
                return React.cloneElement(
                    child,
                    {closeContext: this.props.closeContext}
                );
            }

            else {
                return child;
            }
        });

        return (
            <Collapse isOpen={this.props.context}>
                <ListGroup className='contextList'>
                    {childrenWithProps}
                </ListGroup>
            </Collapse>
        );
    }
}

export class ContextAction extends React.Component {
    constructor(props) {
        super(props);

        this.onClick = this.onClick.bind(this);
    }

    onClick() {
        this.props.closeContext();
        this.props.onClick();
    }

    render() {
        return <li className='contextAction' onClick={this.onClick}>{this.props.children}</li>;
    }
}


ContextMenu.propTypes = {
    context: PropTypes.bool,
    children: PropTypes.node
};

export {Context, ContextMenu};

