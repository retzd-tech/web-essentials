import { atom } from 'recoil';

const createGlobalState = (stateName, stateDefaultValue) => {
  return atom({
    key: stateName,
    default: stateDefaultValue,
  });
};

const fullnameKey = createGlobalState('fullname', '');

export { fullnameKey };
