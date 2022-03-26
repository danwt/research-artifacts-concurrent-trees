import { Grid, GridItem, VStack } from '@chakra-ui/react';
import * as React from 'react';
import { useState } from 'react';
import { ColorModeSwitcher } from "../ColorModeSwitcher";
import Switch from '../view/Switch/Switch';
import Bronson from '../view/Bronson/Bronson'
import BronsonJavaDebug from '../view/BronsonJavaDebug/BronsonJavaDebug'
import JavaGenerated from '../view/JavaGenerated/JavaGenerated'


enum ViewOption {
    Bronson = "Bronson",
    BronsonJavaDebug = "BronsonJavaDebug",
    JavaGenerated = "JavaGenerated",
}

function View({ option }: { option: ViewOption }) {

    if (option === ViewOption.Bronson) {
        return (<Bronson />);
    }
    if (option === ViewOption.BronsonJavaDebug) {
        return (<BronsonJavaDebug />)
    }
    if (option === ViewOption.JavaGenerated) {
        return (<JavaGenerated />)
    }

    return (<>No view selected</>);

}

export default function Dashboard() {

    const [selected, setSelected] = useState(ViewOption.Bronson);

    const options = [ViewOption.Bronson, ViewOption.BronsonJavaDebug, ViewOption.JavaGenerated];

    const labels = Object.values(ViewOption);

    function select(i: number) {
        setSelected(options[i]);
    }

    return (
        <Grid
            minH="98vh"
            templateRows={`repeat(${17}, 1fr)`}
            templateColumns={`repeat(${17}, 1fr)`}
            gap={2}
        >
            <GridItem rowSpan={1} colSpan={1} bg="tomato" >
                <ColorModeSwitcher />
            </GridItem>
            <GridItem colSpan={16} rowSpan={17}>
                <View option={selected} />
            </GridItem>
            <GridItem rowSpan={16} colSpan={1} bg="tomato" >
                <VStack spacing="24px">
                    <Switch labels={labels} onClick={select} />
                </VStack>
            </GridItem>
        </Grid >
    );
}
