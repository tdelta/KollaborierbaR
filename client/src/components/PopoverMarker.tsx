import * as ace_types from 'ace-builds';
import {Range} from 'ace-builds';
import React, {RefObject} from 'react';
import ReactDom from 'react-dom';
import {Popover,PopoverBody} from 'reactstrap';
import AnchoredMarker from './AnchoredMarker';

export default class PopoverMarker{
  private anchor: AnchoredMarker;
  private htmlObject: HTMLElement | null = null;
  private popover: RefObject<MarkerPopover>; 
  private name: string;
  private opacity: number;

  constructor(anchor: AnchoredMarker,name: string){
    this.anchor = anchor;
    this.name = name;
    this.popover = React.createRef<MarkerPopover>();
    this.opacity = 0.5;
  }

  /**
   * Called by ace, when the user interacts with the editor.
   * @param html contains the html code for the marker layer, after all the markers are rendered
   * @param markerLayer the internal marker layer object, containing the logic that displays the markers
   * @param session the current editSession (editor.editSession)
   * @param config the current configuration of the editor
   */
  public update(html: string[],markerLayer: any,session: ace_types.Ace.EditSession,config: any){
    const range: ace_types.Ace.Range = this.anchor.getRange(session);
    console.log(range);
    let stringBuilder: string[] = [];
    if(range.isMultiLine()){
      markerLayer.drawTextMarker(stringBuilder, range, 'remove', config);
    } else {
      markerLayer.drawSingleLineMarker(stringBuilder, range,'remove' , config);
    }
    const markerElements: HTMLCollection = document.getElementsByClassName('remove');
    for(let i:number = 0;i < markerElements.length; i++)
      markerLayer.element.removeChild(markerElements[i]); 

    if(!this.htmlObject)
      this.htmlObject = document.createElement('div');
    this.htmlObject.innerHTML = stringBuilder.join('');

    // Executed when the mouse enters the highlighted area
    this.htmlObject.onmouseenter = () => {
      // If the ref is referring to a present element in the dom, set it to be visible
      if(this.popover.current)
        this.popover.current.setState({isOpen: true});
    };

    // Executed when the mouse leaves the highlighted area
    this.htmlObject.onmouseleave = () => {
      // If the ref is referring to a present element in the dom, set it to be invisible
      if(this.popover.current)
        this.popover.current.setState({isOpen: false});
    };

    this.htmlObject.className = this.anchor.type
    this.htmlObject.style.opacity = this.opacity+'';

    markerLayer.element.appendChild(this.htmlObject);

    ReactDom.render(
      <MarkerPopover
        ref={this.popover}
        target={this.htmlObject}
      >
        <PopoverBody>{this.name}</PopoverBody>
      </MarkerPopover>
      ,this.htmlObject
    );
  }
}

class MarkerPopover extends React.Component<Props,State> {

  constructor(props: Props){
    super(props);
    this.state = {isOpen: false};
  }

  public render(){
    return( 
      <Popover placement="top" isOpen={this.state.isOpen} target={this.props.target}>
        {this.props.children}
      </Popover>
    );
  }
}

interface Props{
  target: HTMLElement;
}

interface State{
  isOpen: boolean;
}
