import React from 'react';
import { Switch, Route } from 'react-router-dom';

import somePage from './Pages/somePage';

const Routes = () => (
  <Switch>
    <Route exact path="/" component={somePage} />
  </Switch>
);

export default Routes;
