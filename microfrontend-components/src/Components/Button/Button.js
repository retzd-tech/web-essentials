import React from "react";
import { Button as ButtonLibrary } from "antd";
import "antd/dist/antd.css";

import Config from "./Button.config";

const Button = (props) => {
  const { text, onClick } = props;

  const renderButton = () => (
    <ButtonLibrary type="primary" shape="round" size={"medium"} onClick={onClick}>
      {text}
    </ButtonLibrary>
  );

  return renderButton();
};

Button.propTypes = Config.propTypes;
Button.defaultProps = Config.defaultProps;

export default Button;
