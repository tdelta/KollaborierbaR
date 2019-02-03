import * as ace_types from 'ace-builds';
import {Range} from 'ace-builds';
import React, {RefObject} from 'react';
import ReactDom from 'react-dom';
import {Tooltip} from 'reactstrap';
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

  public vanish(){
    if(this.opacity > 0.1){
      this.opacity -= 0.05;
    }
  }

  /**
   * Called by ace, when the user interacts with the editor.
   * @param html unused parameter, propably left for compatibility
   * @param markerLayer the internal marker layer object, containing the logic that displays the markers
   * @param session the current editSession (editor.editSession)
   * @param config the current configuration of the editor
   */
  public update(html: string[],markerLayer: any,session: ace_types.Ace.EditSession,config: any){
    let range: ace_types.Ace.Range = this.anchor.getRange(session);
    range = range.toScreenRange(session);
    markerLayer.drawSingleLineMarker(null, range, this.anchor.type+'Marker', config);
      
    let child = markerLayer.element.lastChild;
    console.log(markerLayer.element.children);
    for(let i: number = markerLayer.element.children.length-1;i >= 0;i--){
    console.log(child.style.opacity);
      if(child.className === this.anchor.type+'Marker'
        && !child.style.opacity){
        console.log("break:");
        console.log(child);
        break;
      }
      child = markerLayer.element.children[i];
    }

    const htmlElement = child.cloneNode(true) as HTMLElement;

    // Executed when the mouse enters the highlighted area
    htmlElement.addEventListener('mouseenter',() => {
      // If the ref is referring to a present element in the dom, set it to be visible
      if(this.popover.current)
        this.popover.current.setState({isOpen: true});
    });

    // Executed when the mouse leaves the highlighted area
    htmlElement.addEventListener('mouseout',() => {
      // If the ref is referring to a present element in the dom, set it to be invisible
      if(this.popover.current)
        this.popover.current.setState({isOpen: false});
      const openTooltips:HTMLCollection = document.getElementsByClassName('tooltip') as HTMLCollection;
     // if(openTooltips != null){
     //   for(let i: number = 0;i < openTooltips.length;i++){
     //     if(openTooltips[i] != null && openTooltips[i].parentNode != null){
     //       let tooltipHtml : HTMLElement = openTooltips[i] as HTMLElement;
     //       tooltipHtml.parentNode.removeChild(openTooltips[i]);
     //     }
     //   }
     // }
    });

    htmlElement.style.opacity = this.opacity+'';

    ReactDom.render(
      <MarkerPopover
        ref={this.popover}
        target={htmlElement}
      >
        {this.name}
      </MarkerPopover>
      ,htmlElement
    );

    markerLayer.element.replaceChild(htmlElement,child);
  }
}

class MarkerPopover extends React.Component<Props,State> {

  constructor(props: Props){
    super(props);
    this.state = {isOpen: false};
  }

  public render(){
    return( 
      <Tooltip placement="top" target={this.props.target} isOpen={this.state.isOpen}>
        {this.props.children}
      </Tooltip>
    );
  }
}

interface Props{
  target: HTMLElement;
}

interface State{
  isOpen: boolean;
}
