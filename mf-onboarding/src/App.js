import React from 'react';
import { Router } from 'react-router-dom';

import Routes from './Routes';

const App = ({ history, GlobalAPIProvider }) => (
  <Router history={history}>
    <Routes history={history} GlobalAPIProvider={GlobalAPIProvider}/>
  </Router>
);

export default App;