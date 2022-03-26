import { useState, useCallback, useEffect } from 'react';
import { TableRow } from './Table';
import toDot from '../../util/toDot'
import states from '../../util/cleanErrorTrace'
import { snippetForLabel } from '../../util/labelCodeSnippets'

import _ from 'lodash';

const dotStrings = states.map(it => toDot(it));

/*
NOTE:
The design is as follows:
Map each element of the raw json to a State 
Give each of them an index starting from 0
Use that index as rowIds in the datagrid
*/

const defaultCols = ['id', 'pc', 'left', 'rite', 'parent', 'val'];

const Logic = () => {

    const [jsonValue, setJsonValue] = useState<any>(states[0]);
    const [dotString, setDotString] = useState(`digraph{a->b}`);
    const [tableCols, setTableCols] = useState(defaultCols);
    const [processCodeAtLabels, setProcessCodeAtLabels] = useState<any>([]);
    const [selectedStateIx, setSelectedStateIx] = useState(0);

    const visualizeGraphOfState = _.debounce((id: number) => {
        setDotString(dotStrings[id]);
    }, 50);

    useEffect(useCallback(() => {
        visualizeGraphOfState(selectedStateIx)
        // additionally, set Json
        setJsonValue(states[selectedStateIx]);
    }, [selectedStateIx, visualizeGraphOfState]), [selectedStateIx]);

    const setProcessCodeAtLabelsToShowState = (id: number) => {
        const pc: any = (states[id] as any).pc;
        const procsToFilter = ["initializer", "verifier"];
        let newValue = [];
        for (const [processName, label] of Object.entries(pc)) {
            if (!_.includes(procsToFilter, processName)) {
                const snippet = snippetForLabel(label as string);
                newValue.push({ processName, label, value: snippet })
            }
        }
        setProcessCodeAtLabels(newValue);
    }

    useEffect(useCallback(() => {
        setProcessCodeAtLabelsToShowState(selectedStateIx);
    }, [selectedStateIx]), [selectedStateIx]);

    const updateTableColumnsBasedOnEditorValue = (value: string) => {
        const cols = _.split(value, ',').map(_.trim);
        setTableCols(cols);
    }

    const onEditorValueChange = _.debounce((value: string) => {
        updateTableColumnsBasedOnEditorValue(value);
    }, 1000);

    const onTableRowSelect = (row: TableRow) => {
        setSelectedStateIx(row.id);
    }

    const onTableRowOver = _.debounce((row: TableRow) => {
        // visualizeGraphOfState(row.id);
    }, 50);

    const onTableRowOut = _.debounce((row: TableRow) => {
        // visualizeGraphOfState(selectedStateIx);
    }, 200)

    const onTableColOver = (o: any) => {
        // Intentionally do nothing for now
    }

    return {
        jsonValue,
        dotString,
        onEditorValueChange,
        onTableRowSelect,
        onTableRowOver,
        onTableRowOut,
        onTableColOver,
        tableCols,
        processCodeAtLabels
    }

}

export default Logic;