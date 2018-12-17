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

        this.state = {
            context: false,
        };
    }

    handleRightClick() {
        this.setState({ context: !this.state.context });
    }

    render() {
        console.log(this.state.context)
        const childrenWithProps = React.Children.map(this.props.children, child =>
            React.cloneElement(child, {context: this.state.context})
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

export {Context, ContextMenu};

