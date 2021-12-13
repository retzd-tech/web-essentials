import React from 'react'

import Components from 'microfrontend-components'
import 'microfrontend-components/dist/index.css'

const { Navbar } = Components;

const App = () => {
  return <Navbar menuItems={[
    {
      key: 'dashboard',
      text: 'Dashboard'
    },
    {
      key: 'transfer',
      text: 'Transfer'
    }
  ]}/>
}

export default App
