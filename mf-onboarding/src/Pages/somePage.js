import React, { useState } from 'react';
import Components from 'microfrontend-components';

const { Button, TextInput } = Components;

const somePage = props => {
  const { GlobalStatesProvider, GlobalRoutesProvider } = props;
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
      <Button text="Login" onClick={handleOnClick} />
    </>
  );
};

export default somePage;
