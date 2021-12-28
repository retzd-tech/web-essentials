import 'react-app-polyfill/ie11';
import React from 'react';
import ReactDOM from 'react-dom';

import App from './App';
import { unregister } from './Config/registerServiceWorker';

window.renderMicroOnboarding = (containerId, history, GlobalAPIProvider) => {
  ReactDOM.render(
    <App history={history} GlobalAPIProvider={GlobalAPIProvider}/>,
    document.getElementById(containerId),
  );
  unregister();
};

window.unmountMicroOnboarding = containerId => {
  ReactDOM.unmountComponentAtNode(document.getElementById(containerId));
};
