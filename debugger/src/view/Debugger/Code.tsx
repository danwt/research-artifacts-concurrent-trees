import React from 'react';
import CodeView from '../CodeReader/CodeReader';
import { Grid, GridItem, Heading } from '@chakra-ui/react';
import { defaultSnippet } from '../../util/labelCodeSnippets'

interface ProcessValue {
    label: string;
    processName: string;
    value: string;
}

interface Props {
    values: ProcessValue[];
}

const defaultProps = {
    values: [
        {
            processName: "<no process>",
            label: "<no label> (entire code)",
            value: defaultSnippet
        }
    ]
}

function Code({ values }: Props) {

    const nCols = Math.max(1, values.length);

    if (values.length === 0) {
        values = defaultProps.values;
    }

    return (
        <Grid
            minHeight="100%"
            templateColumns={`repeat(${nCols}, 1fr )`}
            gap={1}
        >
            {values.map((it, i) =>
                <div key={i}>
                    <Heading size="sm" style={{ color: "black", paddingLeft: "3em" }}>
                        {it.processName} at {it.label}
                    </Heading>
                    <CodeView value={it.value} />
                </div>
            )}
            <GridItem  >
            </GridItem>
        </Grid>
    )
}

Code.defaultProps = defaultProps;

export default Code

export type ProcessCodeAtLabel = ProcessValue;
