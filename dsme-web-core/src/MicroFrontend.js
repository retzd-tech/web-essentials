import React, { PureComponent } from 'react';
import axios from 'axios';

import GlobalStates from './GlobalStateManagement';

class MicroFrontend extends PureComponent {
  constructor(props) {
    super(props);
    this.state = {
      isError: false,
      isLoading: true
    };
  }

  attachMicrofrontend = (microfrontendManifest, name) => {
    const { host } = this.props;
    const script = document.createElement('script');
    script.id = name;
    script.src = `${host}${microfrontendManifest['main.js']}`;
    script.onload = this.renderMicroFrontend;
    document.head.appendChild(script);
  };

  fetchMicrofrontend = async (host, scriptId) => {
    try {
      const microfrontendURL = `${host}/asset-manifest.json`;
      const { data: fetchedMicrofrontend } = await axios.get(microfrontendURL);
      this.attachMicrofrontend(fetchedMicrofrontend, scriptId);
    } catch (error) {
      this.setState({ isError: true })
    } finally {
      this.setState({ isLoading: false })
    }
  };

  componentDidMount = async () => {
    const { host, name } = this.props;
    const fetchedMicrofrontend = document.getElementById(name);

    if (fetchedMicrofrontend) {
      this.renderMicroFrontend();
      return;
    }
    return this.fetchMicrofrontend(host, name);
  };

  componentWillUnmount = () => {
    const { name } = this.props;

    window[`unmount${name}`](`${name}-container`);
  };

  renderMicroFrontend = () => {
    const { name, history } = this.props;

    window[`render${name}`](`${name}-container`, history, GlobalStates);
  };

  render() {
    const { name } = this.props;

    return <main id={`${name}-container`} />;
  }
}

export default MicroFrontend;
