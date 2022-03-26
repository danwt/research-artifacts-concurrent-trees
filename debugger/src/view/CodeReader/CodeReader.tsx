import React from 'react'
import Code from '../Code/Code'

interface Props {
    value: string;
}

function CodeReader({ value }: Props) {

    const options = {
        lineNumbers: true,
        readOnly: true
    }


    return (
        <Code options={options} value={value} />
    )
}

export default CodeReader
