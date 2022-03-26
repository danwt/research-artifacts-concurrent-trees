import { Box, Grid, GridItem, Textarea } from '@chakra-ui/react';
import React from 'react';
import Json from '../Json/Json';


interface Props {
    collapseLevel: number;
    jsonValue: any;
    editorValue: string;
    onEditorValueChange: (value: string) => void;
}

const textPlaceholder = 'id,pc,key,val,left,rite,parent'

function Schema({
    collapseLevel,
    jsonValue,
    onEditorValueChange
}: Props) {

    function onChange(value: string) {
        onEditorValueChange(value);
    }

    return (
        <Grid
            minHeight="100%"
            templateColumns={`repeat(${2}, 1fr )`}
            gap={1}
        >
            <GridItem  >
                <Json src={jsonValue} collapsed={collapseLevel} />
            </GridItem>
            <GridItem >
                <Box style={{ position: "fixed" }} >
                    <Textarea resize="both" style={{ color: "black" }} placeholder={textPlaceholder} onChange={(e) => onChange(e.target.value)} />
                </Box>
            </GridItem>
        </Grid>
    )
}

Schema.defaultProps = {
    collapseLevel: 1,
    jsonValue: { "json": { "value": 42 } },
    editorValue: "editorValue",
    onEditorValueChange: (value: string) => { }
}

export default Schema
