import { Box, Heading, HStack } from '@chakra-ui/react'
import React from 'react'
import { wrapContent } from '../../util/toDot'
import Graph from '../Graph/Graph'

const json: any[] = [];

/*
HACK:TODO: deduplicate
*/
const LEFT_COLOR = "crimson";
const RITE_COLOR = "dodgerblue";

interface Edge {
    src: number;
    dst: number;
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

function Element({ k, dotString }: { k: number, dotString: string }) {

    return (
        <Box key={k}>
            <Heading>{k}</Heading>
            <Graph dotString={dotString} width={500} height={400} />
        </Box>
    )
}

function JavaGenerated() {

    return (
        <div>
            <HStack wrap="wrap">
                {json.map((it, i) => {
                    return (<Element k={i} dotString={toDot(it)} />)
                })}
            </HStack>
        </div>
    );
}

export default JavaGenerated;
