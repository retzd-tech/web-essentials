const GlobalRoutesAPI = history => {
  const push = (route) => {
    history.push(route);
  };
  return { push };
};

export { GlobalRoutesAPI }
