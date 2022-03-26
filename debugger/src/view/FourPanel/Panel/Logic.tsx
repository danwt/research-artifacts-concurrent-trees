import React, { useState } from 'react'


function defaultState(): State {
    return {
        bottomOnly: false,
        topOnly: false,
    }
}

interface State {
    bottomOnly: boolean;
    topOnly: boolean;
}

const Logic = () => {

    const [state, setState] = useState(defaultState());

    function setTopOnly() {
        setState(old => {
            return {
                ...old,
                topOnly: !old.topOnly
            }
        })

    }

    function setBottomOnly() {
        setState(old => {
            return {
                ...old,
                bottomOnly: !old.bottomOnly
            }
        })
    }

    return { state, setBottomOnly, setTopOnly, }

}
export default Logic

