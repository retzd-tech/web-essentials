import React, { useEffect } from 'react';
import axios from 'axios';

const MicroFrontend = props => {
  const { name, history, host, GlobalStatesProvider, GlobalRoutesProvider } = props;
  console.log('Debug MF Comp', GlobalStatesProvider);

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
      // setIsError(true);
    } finally {
      // setIsLoading(false);
    }
  };

  useEffect(() => {
    componentDidMount();
    return componentWillUnmount;
  }, []);

  const componentDidMount = async () => {
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
      window[`render${name}`](`${name}-container`, history, GlobalStatesProvider, GlobalRoutesProvider);
    } catch (error) {
      console.log(error);
    }
  };

  return (
    <main id={`${name}-container`} />
  )
};

export default MicroFrontend;
