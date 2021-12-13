import PropTypes from 'prop-types';

const defaultProps = {
  text: '',
  onClick: () => {}
};

const propTypes = {
  text: PropTypes.string,
  onClick: PropTypes.func
};

export default {
  defaultProps,
  propTypes
}