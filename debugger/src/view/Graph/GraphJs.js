import { Graphviz } from 'graphviz-react';
import React from 'react';

export default function GraphJs({ dotString, width, height }) {

    const options = {
        width,
        height
    }

    return (
        <Graphviz dot={dotString} options={options} />
    );
}

