import { Button, HStack } from '@chakra-ui/react';
import React from 'react';

interface ButtonData {
    label: string;
    active: boolean;
    onClick: () => void;

}

interface Props {
    buttonData: ButtonData[];
}

function TopBar({ buttonData }: Props) {
    return (
        <HStack spacing="24px">
            {buttonData.map((it, i) => {
                return (
                    <Button key={i} isActive={it.active} onClick={it.onClick}>{it.label}</Button>
                );
            })}
        </HStack>
    );
}


export default TopBar