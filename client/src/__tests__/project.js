import { mount } from 'enzyme';
import React from 'react';
import Top from '../components/top.tsx';

describe('<App />',() => {
  it('can create and display projects',() => {
    const topBar = mount(<Top />);
    console.log(topBar.find('div'));
  });
});
