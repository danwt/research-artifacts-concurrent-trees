import React, { ReactElement } from 'react'
import TooltipBase from '@material-ui/core/Tooltip';

import { makeStyles, Theme, createStyles } from '@material-ui/core/styles';


const useStyles = makeStyles((theme: Theme) =>
    createStyles({
        customWidth: {
            maxWidth: 400,
            fontSize: 26
        },
    }),
);


interface Props {
    children: ReactElement<any, any>;
    title: string;
}

const defaultPlacement = "top-end"


function Tooltip({ children, title }: Props) {

    const classes = useStyles();

    return (
        <TooltipBase title={title} placement={defaultPlacement} classes={{ tooltip: classes.customWidth }}>
            {children}
        </TooltipBase>);
}


export default Tooltip
