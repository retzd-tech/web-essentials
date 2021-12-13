import 'react-app-polyfill/ie11';
import React from 'react';
import ReactDOM from 'react-dom';

import App from './App';
import { unregister } from './Config/registerServiceWorker';

window.renderMicroRegistration = (containerId, history) => {
  ReactDOM.render(
    <App history={history} />,
    document.getElementById(containerId),
  );
  unregister();
};

window.unmountMicroRegistration = containerId => {
  ReactDOM.unmountComponentAtNode(document.getElementById(containerId));
};
