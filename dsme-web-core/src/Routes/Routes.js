import React from 'react';
import { Switch, Route, withRouter } from 'react-router-dom';
import Components from 'microfrontend-components';
import { createBrowserHistory } from 'history';

import MicroFrontend from '../MicroFrontend';
import Config from '../Config';
import { GlobalStatesAPI } from '../GlobalStatesAPI';
import menuItems from '../Data/navbar-menu-items.json';

const { Navbar } = Components;
const defaultHistory = createBrowserHistory();

const RenderMicroDashboard = ({
  history = defaultHistory,
  GlobalStatesProvider,
  GlobalRoutesProvider,
}) => {
  console.log('DEBUG dashboard: ', GlobalStatesProvider);
  return (
    <>
      <Navbar menuItems={menuItems} />
      <MicroFrontend
        history={history}
        host={Config.microDashboard}
        name="MicroDashboard"
        GlobalStatesProvider={GlobalStatesProvider}
        GlobalRoutesProvider={GlobalRoutesProvider}
      />
    </>
  );
};

const RenderMicroOnboarding = ({
  history = defaultHistory,
  GlobalStatesProvider,
  GlobalRoutesProvider,
}) => {
  console.log('DEBUG onboard: ', GlobalStatesProvider);
  return (
    <MicroFrontend
      history={history}
      host={Config.microOnboarding}
      name="MicroOnboarding"
      GlobalStatesProvider={GlobalStatesProvider}
      GlobalRoutesProvider={GlobalRoutesProvider}
    />
  );
};

const GlobalRoutesAPI = history => {
  const push = (route) => {
    history.push(route);
  };
  return { push };
};

const Routes = props => {
  const { history } = props;
  const { setFullname, fullname } = GlobalStatesAPI();
  const { push } = GlobalRoutesAPI(history);
  const GlobalStatesProvider = {
    setFullname,
    fullname,
  };
  const GlobalRoutesProvider = {
    push,
  };
  return (
    <>
      <p>Hello {fullname}, this is mf-container</p>
      <button onClick={() => props.history.push('/dashboard')}>
        Go to Dashboard from Container
      </button>
      <Switch>
        <Route
          exact
          path="/"
          render={() => (
            <RenderMicroOnboarding
              {...props}
              GlobalStatesProvider={GlobalStatesProvider}
              GlobalRoutesProvider={GlobalRoutesProvider}
            />
          )}
        />
        <Route
          exact
          path="/dashboard"
          render={() => (
            <RenderMicroDashboard
              {...props}
              GlobalStatesProvider={GlobalStatesProvider}
              GlobalRoutesProvider={GlobalRoutesProvider}
            />
          )}
        />
      </Switch>
    </>
  );
};

export default withRouter(Routes);
