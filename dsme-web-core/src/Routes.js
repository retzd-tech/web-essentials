import React from 'react';
import { Switch, Route, withRouter } from 'react-router-dom';
import Components from 'microfrontend-components';
import { createBrowserHistory } from 'history';

import MicroFrontend from './MicroFrontend';
import menuItems from './Data/navbar-menu-items.json';
import Config from './Config';
import { GlobalStatesAPI } from './GlobalAPI/GlobalStatesProvider/GlobalStatesAPI';
import { GlobalRoutesAPI } from './GlobalAPI/GlobalRouteProvider/GlobalRoutesAPI';

const { Navbar } = Components;
const defaultHistory = createBrowserHistory();

const RenderMicroDashboard = ({
  history = defaultHistory,
  GlobalAPIProvider,
}) => {
  return (
    <>
      <Navbar menuItems={menuItems} />
      <MicroFrontend
        history={history}
        host={Config.microDashboard}
        name="MicroDashboard"
        GlobalAPIProvider={GlobalAPIProvider}
      />
    </>
  );
};

const RenderMicroOnboarding = ({
  history = defaultHistory,
  GlobalAPIProvider,
}) => {
  return (
    <MicroFrontend
      history={history}
      host={Config.microOnboarding}
      name="MicroOnboarding"
      GlobalAPIProvider={GlobalAPIProvider}
    />
  );
};

const renderRoute = (Component, props, GlobalAPIProvider) => {
  return <Component {...props} GlobalAPIProvider={GlobalAPIProvider}/>;
};

const Routes = props => {
  const { history } = props;
  const GlobalRoutesProvider = GlobalRoutesAPI(history);
  const GlobalStatesProvider = GlobalStatesAPI();
  const GlobalAPIProvider = { GlobalRoutesProvider, GlobalStatesProvider };
  const name = GlobalStatesProvider.fullname || 'Anonymous';

  return (
    <>
      <p>Hello {name}, this is mf-container</p>
      <Switch>
        <Route
          exact
          path="/"
          render={() =>
            renderRoute(RenderMicroOnboarding, props, GlobalAPIProvider)
          }
        />
        <Route
          exact
          path="/dashboard"
          render={() =>
            renderRoute(RenderMicroDashboard, props, GlobalAPIProvider)
          }
        />
      </Switch>
    </>
  );
};

export default withRouter(Routes);
