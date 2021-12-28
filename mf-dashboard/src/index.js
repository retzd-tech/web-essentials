import 'react-app-polyfill/ie11';
import React from 'react';
import ReactDOM from 'react-dom';

import App from './App';
import { unregister } from './Config/registerServiceWorker';

window.renderMicroDashboard = (containerId, history, GlobalAPIProvider) => {
  ReactDOM.render(
    <App history={history} GlobalAPIProvider={GlobalAPIProvider}/>,
    document.getElementById(containerId),
  );
  unregister();
};

window.unmountMicroDashboard = containerId => {
  ReactDOM.unmountComponentAtNode(document.getElementById(containerId));
};
