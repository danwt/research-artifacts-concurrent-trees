import { DataGrid, GridColDef, GridValueGetterParams } from '@material-ui/data-grid';
import _ from 'lodash';
import React from 'react';
import Tooltip from '../Tooltip/Tooltip'
import { Box } from '@chakra-ui/react'

const defaultRows = [
    { id: 1, lastName: 'Snow', firstName: 'Jon', age: 35 },
    { id: 2, lastName: 'Lannister', firstName: 'Cersei', age: 42 },
    { id: 3, lastName: 'Lannister', firstName: 'Jaime', age: 45 },
    { id: 4, lastName: 'Stark', firstName: 'Arya', age: 16 },
    { id: 5, lastName: 'Targaryen', firstName: 'Daenerys', age: null },
    { id: 6, lastName: 'Melisandre', firstName: null, age: 150 },
    { id: 7, lastName: 'Clifford', firstName: 'Ferrara', age: 44 },
    { id: 8, lastName: 'Frances', firstName: 'Rossini', age: 36 },
    { id: 9, lastName: 'Roxie', firstName: 'Harvey', age: 65 },
];


const defaultColumns: GridColDef[] = [
    { field: 'id', headerName: 'ID', width: 70 },
    { field: 'firstName', headerName: 'First name', width: 130 },
    {
        field: 'lastName', headerName: 'Last name', width: 130,

        renderCell: (params: any) => {
            return (
                <Tooltip title={JSON.stringify(params.row.lastName)} >
                    <span className="table-cell-trucate">{params.row.lastName}</span>
                </Tooltip>
            );
        },
    },
    {
        field: 'age',
        headerName: 'Age',
        type: 'number',
        width: 90,
    },
    {
        field: 'fullName',
        headerName: 'Full name',
        description: 'This column has a value getter and is not sortable.',
        sortable: false,
        width: 160,
        valueGetter: (params: GridValueGetterParams) =>
            `${params.getValue('firstName') || ''} ${params.getValue('lastName') || ''}`,
    },
];



function multiply(arr: any[]) {
    let ret: any = _.times(3, () => _.cloneDeep(defaultRows));
    ret = _.flatten(ret);
    ret.forEach((it: any, i: number) => {
        it.id = i;
    })
    return ret;
}

interface Row {
    id: number;
}

interface Props {
    cols: GridColDef[];
    rows: Row[];
    onRowSelect: (row: Row) => void;
    onRowOver: (row: Row) => void;
    onRowOut: (row: Row) => void;
    onColumnHeaderOver: (col: any) => void;
    onCellOver: (col: any) => void;
}

const rowHeight = 42;
const rowsPerPageOptions = [100, 200, 300];

function Table({
    cols,
    rows,
    onRowSelect,
    onRowOver,
    onRowOut,
    onColumnHeaderOver,
    onCellOver
}: Props) {


    function onRowSelectToUse(o: any) {
        onRowSelect(o.data as Row);
    }

    function onRowOverToUse(o: any) {
        onRowOver(o.row as Row);
    }

    function onRowOutToUse(o: any) {
        onRowOut(o.row as Row);
    }

    function onColumnHeaderOverToUse(o: any) {
        onColumnHeaderOver(o);
    }

    function onCellOverToUse(o: any) {
        onCellOver(o);
    }

    return (
        <DataGrid
            rows={rows}
            columns={cols}
            rowsPerPageOptions={rowsPerPageOptions}
            autoHeight={true}
            rowHeight={rowHeight}
            onRowSelected={onRowSelectToUse}
            onRowOver={onRowOverToUse}
            onRowOut={onRowOutToUse}
            density="compact"
            onColumnHeaderOver={onColumnHeaderOverToUse}
            onCellOver={onCellOverToUse}
        />
    )
}

Table.defaultProps = {
    cols: [],//defaultColumns,
    rows: [],//multiply(defaultRows),
    onRowSelect: (row: Row) => { },
    onRowOver: (row: Row) => { },
    onRowOut: (row: Row) => { },
    onColumnHeaderOver: (col: any) => { },
    onCellOver: (col: any) => { }
}


export default Table
export type { Row };

