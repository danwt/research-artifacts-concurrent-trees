import { GridColDef } from '@material-ui/data-grid';
import _ from 'lodash';
import React from 'react';
import states from '../../util/cleanErrorTrace';
import TableView, { Row } from '../Table/Table';
import Tooltip from '../Tooltip/Tooltip';
import { Box } from '@chakra-ui/react'

function keysUnion(a: any[]) {
    return Object.keys(Object.assign({}, ...a));
}

const allKeys: string[] = keysUnion(states);

function initHeaderToAllColsMap() {
    let ret: any = {};
    allKeys.forEach((it, i) => {
        ret[it] = i;
    });
    return ret;
}

const headerToAllColsIndexMap = initHeaderToAllColsMap();


function cleanValue(value: any) {
    if (!_.isNumber(value)) {
        const string = JSON.stringify(value);
        return string;
    }
    return value;
}

function initRows(states: any[]): TableRow[] {
    const filtered = states.map(it => _.pick(it, allKeys));//TODO: does this create nulls?
    const clean = filtered.map(it => {
        return _.mapValues(it, cleanValue);
    });
    return (clean as unknown) as TableRow[];
}

function renderCell(field: string) {
    return (params: any) => {
        const value = params.row[field];
        return (
            <Tooltip title={value} >
                <span className="table-cell-trucate">{value}</span>
            </Tooltip>
        );
    }
}

function addTooltips(col: GridColDef) {
    return {
        ...col, renderCell: renderCell(col.field)
    }
}



function initCols(states: any[]): GridColDef[] {
    const ret = allKeys.map(it => {
        let ret = { field: it, headerName: it, width: 170 };
        //HACK: special cases...
        const specialWidth: any = { 'pc': 480, 'locked': 350, height: 500 };
        if (_.includes(Object.keys(specialWidth), it)) {
            ret.width = specialWidth[it];
        }
        return ret;
    })
    return ret.map(addTooltips);
}

const allRows = initRows(states);
const allCols = initCols(states);

function selectColsSubset(headers: string[]): GridColDef[] {
    let ret: GridColDef[] = [];
    headers.forEach(it => {
        let colIx = headerToAllColsIndexMap[it];
        if (colIx !== undefined) {
            ret.push(allCols[colIx]);
        }
    })
    return ret;
}

function Table({ colsToShow, ...props }: any) {

    return (
        <Box fontSize="26">
            <TableView rows={allRows} cols={selectColsSubset(colsToShow)} {...props} />
        </Box>
    );
}

export default Table;

export type TableRow = Row;