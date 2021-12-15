import React, { useState, useEffect } from 'react';
import axios from 'axios';

import { GlobalStates } from './GlobalStateManagement';

const MicroFrontend = props => {
  const { name, history, host } = props;
  const [isError, setIsError] = useState(false);
  const [isLoading, setIsLoading] = useState(true);
  const [stateKey, setStateKey] = useState('');
  const [requestedGlobalState, setRequestedGlobalState] = GlobalStates(stateKey, '');

  const attachMicrofrontend = (microfrontendManifest, name) => {
    const script = document.createElement('script');
    script.id = name;
    script.src = `${host}${microfrontendManifest['main.js']}`;
    script.onload = renderMicroFrontend;
    document.getElementById('root').appendChild(script);
  };

  const fetchMicrofrontend = async (host, scriptId) => {
    try {
      const microfrontendURL = `${host}/asset-manifest.json`;
      const { data: fetchedMicrofrontend } = await axios.get(microfrontendURL);
      attachMicrofrontend(fetchedMicrofrontend, scriptId);
    } catch (error) {
      setIsError(true);
    } finally {
      setIsLoading(false);
    }
  };

  useEffect(() => {
    componentDidMount();
    return componentWillUnmount;
  }, []);

  const componentDidMount = async () => {
    const { host, name } = props;
    const fetchedMicrofrontend = document.getElementById(name);

    if (fetchedMicrofrontend) {
      renderMicroFrontend();
      return;
    }
    return fetchMicrofrontend(host, name);
  };

  const componentWillUnmount = () => {
    try {
      window[`unmount${name}`](`${name}-container`);
    } catch (error) {
      console.log(error);
    }
  };

  const renderMicroFrontend = () => {
    try {
      window[`render${name}`](`${name}-container`, history);
    } catch (error) {
      console.log(error);
    }
  };

  return (
    <>
      <button
        onClick={() => {
          setStateKey('name');
          console.log('DEBUG: ', requestedGlobalState);
        }}
      >
        Get Global State
      </button>
      <button
        onClick={() => {
          setStateKey('name');
          setRequestedGlobalState('Modified name ' + new Date().getMilliseconds());
        }}
      >
        Update Global State
      </button>
      {requestedGlobalState && <p>{requestedGlobalState.name}</p>}
    </>
  );
};

export default MicroFrontend;
