import React from 'react';
import { Switch, Route } from 'react-router-dom';

import SomePage from './Pages/somePage';

const Routes = (props) => (
  <Switch>
    <Route exact path="/" render={() => <SomePage {...props}/>} />
    <Route exact path="/dashboard" render={() => <>ok</>} />
  </Switch>
);

export default Routes;
