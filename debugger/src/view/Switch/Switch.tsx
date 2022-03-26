import React from 'react'
import { Button } from '@chakra-ui/react';


interface Props {
    labels: string[];
    onClick: (i: number) => void;
}

function Switch({ labels, onClick }: Props) {
    return (<>
        {
            labels.map((it, i) => {
                return <Button key={i}
                    onClick={() => onClick(i)}
                >{it}</Button>

            })
        }
    </>);

}

export default Switch
