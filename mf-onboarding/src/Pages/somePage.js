import React, { useState } from 'react';
import Components from 'microfrontend-components';
import { withRouter } from 'react-router-dom';

const { Button, TextInput } = Components;

const somePage = props => {
  const {
    GlobalAPIProvider: { GlobalStatesProvider, GlobalRoutesProvider }
  } = props;
  const [inputName, setInputName] = useState('');

  const handleOnClick = () => {
    try {
      GlobalStatesProvider.setFullname(inputName);
      GlobalRoutesProvider.push('dashboard');
    } catch (error) {
      console.log(error);
    }
  };

  const handleOnChange = e => {
    const inputtedName = e.target.value;
    setInputName(inputtedName);
  };

  return (
    <>
      <div>Some Page of mf-onboarding</div>
      <TextInput placeholder="Input your name" onChange={handleOnChange} />
      <Button
        text="Login and go to mf-dashboard page"
        onClick={handleOnClick}
      />
    </>
  );
};

export default withRouter(somePage);
