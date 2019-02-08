import * as ace_types from 'ace-builds';
import { Range } from 'ace-builds';
import React, { RefObject } from 'react';
import ReactDom from 'react-dom';
import { Tooltip } from 'reactstrap';
import AnchoredMarker from './AnchoredMarker';

export default class PopoverMarker {
  private anchor: AnchoredMarker;
  private htmlObject: HTMLElement | null = null;
  private popover: RefObject<MarkerPopover>;
  private name: string;
  private opacity: number;

  constructor(anchor: AnchoredMarker, name: string, opacity: number) {
    this.anchor = anchor;
    this.name = name;
    this.popover = React.createRef<MarkerPopover>();
    this.opacity = opacity;
  }

  public vanish() {
    if (this.opacity > 0.1) {
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
  public update(
    html: string[],
    markerLayer: any,
    session: ace_types.Ace.EditSession,
    config: any
  ) {
    let range: ace_types.Ace.Range = this.anchor.getRange(session);
    range = range.toScreenRange(session);
    if(range.isMultiLine()){
      markerLayer.drawTextMarker(
        null,
        range,
        this.anchor.type + 'Marker',
        config
      );
    } else {
      markerLayer.drawSingleLineMarker(
        null,
        range,
        this.anchor.type + 'Marker',
        config
      );
    }

    for (let i: number = markerLayer.element.children.length - 1; i >= 0; i--) {
      let child = markerLayer.element.children[i];
      if (
        child.className.includes(`${this.anchor.type}Marker`) &&
        !child.style.opacity
      ) {
        const htmlElement = child.cloneNode(true) as HTMLElement;
        // Executed when the mouse enters the highlighted area
        htmlElement.addEventListener('mouseenter', () => {
          // If the ref is referring to a present element in the dom, set it to be visible
          if (this.popover.current != null){
            this.popover.current.setState({ isOpen: true });
            window.setTimeout(this.popover.current.hide.bind(this.popover.current),4000);
          }
        });

        // Executed when the mouse leaves the highlighted area
        htmlElement.addEventListener('mouseout', () => {
          // If the ref is referring to a present element in the dom, set it to be invisible
          if (this.popover.current)
            this.popover.current.setState({ isOpen: false });
        });

        htmlElement.style.opacity = this.opacity + '';

        ReactDom.render(
          <MarkerPopover ref={this.popover} target={htmlElement}>
            {this.name}
          </MarkerPopover>,
          htmlElement
        );

        markerLayer.element.replaceChild(htmlElement, child);
      }
    }
  }
}

class MarkerPopover extends React.Component<Props, State> {
  constructor(props: Props) {
    super(props);
    this.state = { isOpen: false };
  }

  public render() {
    return (
      <Tooltip
        placement="top"
        target={this.props.target}
        isOpen={this.state.isOpen}
      >
        {this.props.children}
      </Tooltip>
    );
  }

  public hide(){
    this.setState({isOpen: false});
  }
}

interface Props {
  target: HTMLElement;
}

interface State {
  isOpen: boolean;
}
