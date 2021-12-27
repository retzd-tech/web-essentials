import React from 'react';
import { Router } from 'react-router-dom';

import Routes from './Routes';

const App = ({ history, GlobalStatesProvider, GlobalRoutesProvider}) => {
  console.log('DEBUG App dash: ', GlobalStatesProvider);
  return (
  <Router history={history}>
    <Routes history={history} GlobalStatesProvider={GlobalStatesProvider} GlobalRoutesProvider={GlobalRoutesProvider} />
  </Router>
)};

export default App;