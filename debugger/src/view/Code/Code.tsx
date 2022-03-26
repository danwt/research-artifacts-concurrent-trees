// import 'codemirror/lib/codemirror.css';
import 'codemirror/theme/xq-light.css';
import React from 'react';
import { Controlled as CodeMirror } from 'react-codemirror2';
import './codemirror.css';

require('codemirror/mode/pascal/pascal');
require('codemirror/mode/clike/clike');

const defaultBaseOptions = {
    mode: 'clike',
    theme: 'xq-light',
    tabSize: 2,
    lineWrapping: true,
};

interface Options {
    lineNumbers?: boolean,
    readonly?: boolean,
}

const defaultOptions: Options = {
    ...defaultBaseOptions,
    lineNumbers: false,
    readonly: false
}

// const defaultValue = tla.content;
const defaultValue = "";

type OnBeforeChange = (editor: any, data: any, value: string) => void;

interface Props {
    onBeforeChange: OnBeforeChange,
    value: string,
    options: Options
}

function defaultBeforeChange(editor: any, data: any, value: string) {
    // Intentionally empty as CodeMirror requires handler

}

function Code({ value, options, onBeforeChange }: Props) {

    const optionsToUse = { ...defaultBaseOptions, ...options };

    return (
        <CodeMirror
            value={value}
            options={optionsToUse}
            onBeforeChange={onBeforeChange}
            onChange={(editor, data, value) => {
            }}
        />
    )
}

Code.defaultProps = {
    value: defaultValue,
    options: defaultOptions,
    onBeforeChange: defaultBeforeChange
}

export default Code
