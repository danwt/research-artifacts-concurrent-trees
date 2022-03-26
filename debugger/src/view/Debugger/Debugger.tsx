import React from 'react';
import FourPanel from '../FourPanel/FourPanel';
import Code from './Code';
import Graph from './Graph';
import Logic from './Logic';
import Schema from './Schema';
import Table from './Table';


function Debugger() {

    const {
        jsonValue,
        onEditorValueChange,
        dotString,
        onTableRowSelect,
        onTableRowOver,
        onTableRowOut,
        onTableColOver,
        tableCols,
        processCodeAtLabels
    } = Logic();

    return (
        <FourPanel
            LeftTop={<Table
                colsToShow={tableCols}
                onRowSelect={onTableRowSelect}
                onRowOver={onTableRowOver}
                onRowOut={onTableRowOut}
                onColumnHeaderOver={onTableColOver}
            />
            }
            LeftBottom={<Schema
                jsonValue={jsonValue}
                onEditorValueChange={onEditorValueChange} />
            }
            RiteTop={<Code
                values={processCodeAtLabels}
            />}
            RiteBottom={<Graph
                dotString={dotString} />}
        />
    )
}

export default Debugger
