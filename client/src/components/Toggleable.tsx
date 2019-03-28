import React from 'react';

/**
 * Component which is used to encapsulate another component whose visibility can
 * then be controlled by setting the {@link this.props.isVisible} property of
 * this component.
 */
export default class Toggleable extends React.Component<Props, {}> {
  /* By default, there is no (css) class set */
  public static defaultProps = {
    className: '',
  };

  /**
   * React lifecycle rendering method.
   * {@see https://reactjs.org/docs/react-component.html#render}
   *
   * See constructor documentation for information on what is being rendered.
   */
  public render(): React.ReactNode {
    const display = this.props.isVisible ? '' : 'none';

    return (
      <div className={this.props.className} style={{ display }}>
        {this.props.children}
      </div>
    );
  }
}

interface Props {
  /** decides, whether the children of {@link Toggleable} shall be visible or not */
  isVisible: boolean;
  /** children displayed within {@link Toggleable}, given {@link isVisible} is `true` */
  children: React.ReactNode;
  /** custom (css) class name(s), which can be applied to {@link Toggleable} */
  className: string;
}
