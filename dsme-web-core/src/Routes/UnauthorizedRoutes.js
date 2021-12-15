import React, { useState } from 'react';
import { Switch, Route } from 'react-router-dom';

import MicroFrontend from '../MicroFrontend';
import Config from '../Config';

import { GlobalStates } from './../GlobalStateManagement';

const renderMicroOnboarding = ({ history }) => (
  <MicroFrontend
    history={history}
    host={Config.microOnboarding}
    name="MicroRegistration"
  />
);

const Routes = () => {
  useState(() => {
    const { globalData, setGlobalData } = GlobalStates(
      'globalData',
      'some global data',
    );
  }, []);
  return (
    <Switch>
      <Route exact path="/" component={renderMicroOnboarding} />
    </Switch>
  );
};

export default Routes;
