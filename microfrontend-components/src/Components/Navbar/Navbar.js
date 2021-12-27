import React, { useState } from "react";
import { Menu } from "antd";
import "antd/dist/antd.css";

import Config from './Navbar.config'

const Navbar = (props) => {
  const { menuItems } = props;
  const [tab, setTab] = useState("dashboard");

  const handleClick = ({ key: chosenTab }) => {
    setTab(chosenTab);
  };

  const renderMenuItem = (key, text) => <Menu.Item key={key}>{text}</Menu.Item>;

  const renderMenuItems = (menuItems) => {
    return menuItems.map((menu) => {
      const { key, text } = menu;
      return renderMenuItem(key, text);
    });
  };

  return (
    <Menu onClick={handleClick} selectedKeys={[tab]} mode="horizontal">
      {renderMenuItems(menuItems)}
    </Menu>
  );
};

Navbar.propTypes = Config.propTypes
Navbar.defaultProps = Config.defaultProps

export default Navbar;
