import React from 'react';
import { Router } from 'react-router-dom';
import { createBrowserHistory } from 'history';

import Routes from './Routes';

const App = ({ GlobalStatesProvider, history, GlobalRoutesProvider }) => (
  <Router history={history}>
    <Routes history={history} GlobalRoutesProvider={GlobalRoutesProvider} GlobalStatesProvider={GlobalStatesProvider}/>
  </Router>
);

export default App;