import { useRecoilState } from 'recoil';

const useGlobalState = (state) => {
  try {
    const [stateValue, setState] = useRecoilState(state);

    return [stateValue, setState];
  } catch (error) {
    console.log(error);
  }
};

export { useGlobalState };
