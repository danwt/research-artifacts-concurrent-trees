import { Grid, GridItem } from '@chakra-ui/react';
import React from 'react';
import Logic from './Logic';
import Panel from './Panel/Panel';



const light1 = "whitesmoke";
const light2 = "snow";
const light3 = "seashell";
const light4 = "ghostwhite";
const light5 = "aliceblue";
const light6 = "azure";
const med1 = "lightskyblue";
const med2 = "papayawhip";

interface Props {
    LeftTop: JSX.Element;
    LeftBottom: JSX.Element;
    RiteTop: JSX.Element;
    RiteBottom: JSX.Element;
}

function FourPanel({ LeftTop, LeftBottom, RiteBottom, RiteTop }: Props) {


    const { state, setLeftOnly, setRiteOnly } = Logic();

    const leftCols = state.leftOnly ? 16 : 7;
    const riteCols = state.riteOnly ? 16 : 9;

    return (
        <Grid
            minHeight="100%"
            templateColumns={`repeat(${16}, 1fr )`}
            gap={1}
        >
            {!state.riteOnly &&
                <GridItem colSpan={leftCols} bg={med1} >
                    <Panel Top={LeftTop} Bottom={LeftBottom} onFullToggle={setLeftOnly} isFull={state.leftOnly} />
                </GridItem>
            }
            {!state.leftOnly &&
                <GridItem colSpan={riteCols} bg={med1} >
                    <Panel Top={RiteTop} Bottom={RiteBottom} onFullToggle={setRiteOnly} isFull={state.riteOnly} />
                </GridItem>
            }
        </Grid>
    );
}

export default FourPanel;
