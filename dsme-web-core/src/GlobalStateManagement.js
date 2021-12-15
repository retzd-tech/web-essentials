import { useRecoilState, atom } from 'recoil';

import { StringUtils } from './Utils';

const GlobalStates = (stateName, defaultValue) => {
  try {
    const stateAtom = atom({
      key: stateName,
      default: defaultValue,
    });

    const [recoilState, setRecoilState] = useRecoilState(stateAtom);
    const setState = `set${StringUtils.capitalizeText(stateName)}`;

    return [
      recoilState,
      setRecoilState,
    ];
  } catch (error) {
    console.log(error);
  }
};

export { GlobalStates };
