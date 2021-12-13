import React from 'react';
import { Switch, Route } from 'react-router-dom';

import MicroFrontend from '../MicroFrontend';
import Config from '../Config';

const renderMicroOnboarding = ({ history }) => (
  <MicroFrontend
    history={history}
    host={Config.microOnboarding}
    name="MicroRegistration"
  />
);

const Routes = () => (
  <Switch>
    <Route exact path="/" component={renderMicroOnboarding} />
  </Switch>
);

export default Routes;
