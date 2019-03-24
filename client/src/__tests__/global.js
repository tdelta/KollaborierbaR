import { mount } from 'enzyme';
import React from 'react';
import App from '../components/app.jsx';
import Editor from '../components/editor.tsx';
import Top from '../components/top.tsx';
import Sidebar from '../components/sidebar/sidebar.jsx';

describe('<App />', () => {
  it('renders all components without crashing',() => {
    const app = mount(<App />,{attachTo: document.body});
    expect(app.find(Sidebar)).toHaveLength(1);
    expect(app.find(Top)).toHaveLength(1);
    expect(app.find(Editor)).toHaveLength(1);
  });
});
