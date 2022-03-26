import React from 'react'
import ReactJson from 'react-json-view'



function Json(props: any) {
    const theme = "summerfruit:inverted";
    return (
        <ReactJson {...props} theme={theme} />
    )
}

export default Json
