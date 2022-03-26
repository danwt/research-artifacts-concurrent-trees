import React, { useState } from 'react'

function defaultState(): State {
    return {
        leftOnly: false,
        riteOnly: false,
    }
}

interface State {
    leftOnly: boolean;
    riteOnly: boolean;
}

const Logic = () => {

    const [state, setState] = useState(defaultState());

    function setRiteOnly() {
        setState(old => {
            return {
                ...old,
                riteOnly: !old.riteOnly
            }
        })

    }

    function setLeftOnly() {
        setState(old => {
            return {
                ...old,
                leftOnly: !old.leftOnly
            }
        })
    }

    return { state, setLeftOnly, setRiteOnly, }

}

export default Logic
