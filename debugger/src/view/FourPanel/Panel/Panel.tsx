import { Box, Grid, GridItem } from '@chakra-ui/react';
import { default as React } from 'react';
import TopBar from '../TopBar/TopBar';
import Logic from './Logic';

const light1 = "whitesmoke";
const light2 = "snow";
const light3 = "seashell";
const light4 = "ghostwhite";
const light5 = "aliceblue";
const light6 = "azure";
const med1 = "lightskyblue";
const med2 = "papayawhip";


interface Props {
    Top: JSX.Element;
    Bottom: JSX.Element;
    onFullToggle: () => void;
    isFull: boolean
}

function Panel({ Top, Bottom, isFull: boolean, onFullToggle = () => { } }: Props) {

    const { state, setBottomOnly, setTopOnly } = Logic();

    const topRows = state.topOnly ? 16 : 9;
    const bottomRows = state.bottomOnly ? 16 : 7;

    const topDefaultHeight = 1000;
    const bottomDefaultHeight = 500;
    const sumHeight = topDefaultHeight + bottomDefaultHeight

    const topHeight = state.topOnly ? sumHeight : topDefaultHeight;
    const bottomHeight = state.topOnly ? sumHeight : bottomDefaultHeight;

    return (
        <Grid
            minHeight="100%"
            templateRows={`repeat(${17}, 1fr)`}
            gap={1}
        >
            <GridItem bg={med1} >
                <TopBar
                    buttonData={
                        [{
                            label: "Full Screen",
                            active: true,
                            onClick: onFullToggle
                        }, {
                            label: "Top Only",
                            active: state.topOnly,
                            onClick: setTopOnly
                        }, {
                            label: "Bottom Only",
                            active: state.bottomOnly,
                            onClick: setBottomOnly
                        }]
                    }
                />
            </GridItem>
            {!state.bottomOnly &&
                <GridItem rowSpan={topRows} bg={light2} >
                    <Box overflowY="scroll" maxHeight={topHeight} >
                        {Top}
                    </Box>
                </GridItem>
            }
            {!state.topOnly &&
                <GridItem rowSpan={bottomRows} bg={light1} >
                    <Box overflowY="scroll" maxHeight={bottomHeight} fontSize="16">
                        {Bottom}
                    </Box>
                </GridItem>
            }
        </Grid >
    );

}


export default Panel
