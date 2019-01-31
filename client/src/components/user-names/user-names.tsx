import React, { RefObject, ReactSVG } from 'react';
import './animals.css';
import { UncontrolledTooltip } from 'reactstrap';

export default class Usernames extends React.Component<Props, State> {
    constructor(props: Props) {
        super(props);

  }

private testArray(){
    var test = [
                {"name": "Peter", "color": 0},
                {"name": "Lustig", "color": 1},
                {"name": "Mark", "color": 2},
                {"name": "BigJ", "color": 3},
                {"name": "Hallo", "color": 4},
                {"name": "lalalala", "color": 5}
               ];
    return test;
  }

public render(){
  return( 
    <>
                {
                    this.testArray().map((iterator) => 
                  <> 
                  <span className="login-text" id={iterator.name}> 
                    <div className={"circle" + iterator.color}></div>
                   </span>
                    <UncontrolledTooltip delay={{ show: 0, hide: 0 }} placement="bottom" target={iterator.name}>
                      {iterator.name}
                    </UncontrolledTooltip>
                  </>
                    )
                } 
    </>
  );
}
}
interface Props{

}

interface State{

}
