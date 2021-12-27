import { fullnameKey } from './GlobalStates';
import { useGlobalState } from './useGlobalState';

const GlobalStatesAPI = () => {
  const [fullname, setFullname] = useGlobalState(fullnameKey);
  return {
    fullname,
    setFullname,
  };
};

export { GlobalStatesAPI }
