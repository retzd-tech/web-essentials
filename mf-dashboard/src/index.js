import 'react-app-polyfill/ie11';
import React from 'react';
import ReactDOM from 'react-dom';

import App from './App';
import { unregister } from './Config/registerServiceWorker';

window.renderMicroDashboard = (containerId, history, GlobalStatesProvider, GlobalRoutesProvider) => {
  ReactDOM.render(
    <App history={history} GlobalStatesProvider={GlobalStatesProvider} GlobalRoutesProvider={GlobalRoutesProvider}/>,
    document.getElementById(containerId),
  );
  unregister();
};

window.unmountMicroDashboard = containerId => {
  ReactDOM.unmountComponentAtNode(document.getElementById(containerId));
};
