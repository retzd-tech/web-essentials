import React from 'react';
import { BrowserRouter } from 'react-router-dom';
import { RecoilRoot } from 'recoil';

import UnauthorizedRoutes from './Routes/UnauthorizedRoutes';
import AuthorizedRoutes from './Routes/AuthorizedRoutes';

const App = () => (
  <RecoilRoot>
    <BrowserRouter>
      <React.Fragment>
        <UnauthorizedRoutes />
        <AuthorizedRoutes />
      </React.Fragment>
    </BrowserRouter>
  </RecoilRoot>
);

export default App;
