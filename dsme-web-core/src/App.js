import React from 'react';
import { BrowserRouter } from 'react-router-dom';

import UnauthorizedRoutes from './Routes/UnauthorizedRoutes';
import AuthorizedRoutes from './Routes/AuthorizedRoutes';

const App = () => (
  <BrowserRouter>
    <React.Fragment>
      <UnauthorizedRoutes />
      <AuthorizedRoutes />
    </React.Fragment>
  </BrowserRouter>
);

export default App;
