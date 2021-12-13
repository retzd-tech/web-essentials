import React from 'react';
import Components from 'microfrontend-components';

const { Button } = Components;

const somePage = props => {
  const handleOnClick = () => {
      props.history.push('dashboard');
  };

  return (
    <>
      <div>Some Page of mf-onboarding</div>
      <Button text="Login" onClick={handleOnClick} />
    </>
  );
};

export default somePage;
