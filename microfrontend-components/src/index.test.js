import '@testing-library/jest-dom'
import * as React from 'react'
import { render, fireEvent, screen } from '@testing-library/react'
import renderer from 'react-test-renderer'

import HiddenMessage from '.'

describe('HiddenMessage', () => {
  const testMessage = 'Test Message'

  describe('#render', () => {
    it('should render as expected as snapshot', () => {
      const HiddenMessageSnapshot = renderer
        .create(<HiddenMessage>{testMessage}</HiddenMessage>)
        .toJSON()

      expect(HiddenMessageSnapshot).toMatchSnapshot()
    })
  })

  describe('#click', () => {
    it('should show no message at first', () => {
      render(<HiddenMessage>{testMessage}</HiddenMessage>)

      expect(screen.queryByText(testMessage)).toBeNull()
    })

    it('should show the hidden message when the checklist input is selected', () => {
      render(<HiddenMessage>{testMessage}</HiddenMessage>)

      expect(screen.queryByText(testMessage)).toBeNull()
      fireEvent.click(screen.getByLabelText(/show/i))
      expect(screen.getByText(testMessage)).toBeInTheDocument()
    })
  })
})
