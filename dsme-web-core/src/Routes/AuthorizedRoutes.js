import React from 'react';
import { Switch, Route } from 'react-router-dom';
import Components from 'microfrontend-components';

import MicroFrontend from '../MicroFrontend';
import Config from '../Config';
import menuItems from '../Data/navbar-menu-items.json';

const { Navbar } = Components;

const renderMicroDashboard = ({ history }) => (
  <>
    <Navbar menuItems={menuItems} />
    <MicroFrontend
      history={history}
      host={Config.microDashboard}
      name="MicroDashboard"
    />
  </>
);

const Routes = () => (
  <Switch>
    <Route exact path="/dashboard" component={renderMicroDashboard} />
  </Switch>
);

export default Routes;
