import React from 'react';
import { Switch, Route } from 'react-router-dom';

import SomeComponent from './Components/SomeComponent';

const Routes = () => (
  <Switch>
    <Route exact path="/dashboard" component={SomeComponent} />
  </Switch>
);

export default Routes;
