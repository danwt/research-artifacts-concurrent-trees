import React from 'react';
import GraphView from '../Graph/Graph';
import { Box } from '@chakra-ui/react'

interface Props {
    dotString: string;
}

function Graph({ dotString }: Props) {
    // HACK: maxHeight should be dynamic and dependent on parent
    return (<Box padding="2em">
        <GraphView dotString={dotString} height={475} />;
    </Box>);
}

const MemoizedGraph = React.memo(Graph);

export default MemoizedGraph;
