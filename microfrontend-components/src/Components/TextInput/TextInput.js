import React from "react";
import { Input as TextInputLibrary } from "antd";
import { UserOutlined } from '@ant-design/icons';
import "antd/dist/antd.css";

import Config from "./TextInput.config";

const TextInput = (props) => {
  const { placeholder, onChange, value } = props;

  const renderTextInput = () => (
    <TextInputLibrary
      placeholder={placeholder}
      prefix={<UserOutlined className="site-form-item-icon" />}
      onChange={onChange}
    />
  );

  return renderTextInput();
};

TextInput.propTypes = Config.propTypes;
TextInput.defaultProps = Config.defaultProps;

export default TextInput;
