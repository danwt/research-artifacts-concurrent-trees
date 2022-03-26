import React, { useState } from 'react'
import Code from '../Code/Code'

type OnChange = (value: string) => void;

interface Props {
    onChange: OnChange
}

const Logic = () => {
    const [value, setValue] = useState("");

    return { value, setValue }
}

function CodeEditor({ onChange }: Props) {

    const { value, setValue } = Logic();

    const options = {
        lineNumbers: true,
        readOnly: false
    }

    function onChangeToUse(editor: any, data: any, newValue: string) {
        setValue(newValue);
        onChange(newValue);
    }

    return (
        <Code options={options} value={value} onBeforeChange={onChangeToUse} />
    )
}

export default CodeEditor
