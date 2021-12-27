import React from 'react';
import { Switch, Route } from 'react-router-dom';

import SomeComponent from './Components/SomeComponent';

const Routes = (props) => (
  <Switch>
    <Route exact path="/dashboard" render={() => <SomeComponent {...props}/>} />
  </Switch>
);

export default Routes;
