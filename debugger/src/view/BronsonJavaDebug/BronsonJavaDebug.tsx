import React from 'react'
import Graph from '../Graph/Graph'

import { wrapContent } from '../../util/toDot'
import { Heading } from '@chakra-ui/react'

const LEFT_COLOR = "crimson";
const RITE_COLOR = "dodgerblue";
const PARENT_COLOR = "darkseagreen2";

interface Edge {
    src: string;
    dst: string;
    left: boolean;
}


function edge(e: Edge): string {
    return `${e.src}->${e.dst} [style=bold, color=${e.left ? LEFT_COLOR : RITE_COLOR}];\n`
}

function toDot(edges: Edge[]): string {
    let content = "";
    edges.forEach(it => {
        content += edge(it);
    });
    return wrapContent(content);
}

function BronsonJavaDebug() {

    return (
        <div>
            <Heading>0</Heading>
            {/* <Graph dotString={toDot(json0 as Edge[])} height={700} /> */}
            <Heading>1</Heading>
            {/* <Graph dotString={toDot(json1 as Edge[])} height={700} /> */}
            <Heading>2</Heading>
            {/* <Graph dotString={toDot(json2 as Edge[])} height={700} /> */}
        </div>
    )
}

export default BronsonJavaDebug
