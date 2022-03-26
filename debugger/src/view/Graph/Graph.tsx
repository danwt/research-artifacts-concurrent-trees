import React from 'react';
import GraphJs from './GraphJs.js';

interface Graph {
	dotString: string;
	width: number | string;
	height: number | string;
}


const example = `
digraph finite_state_machine {
	rankdir=LR;
	size="8,5"
	node [shape = doublecircle]; 0 3 4 8;
	node [shape = circle];
	0 -> 2 [label = "SS(B)"];
	0 -> 1 [label = "SS(S)"];
	1 -> 3 [label = "S($end)"];
	2 -> 6 [label = "SS(b)"];
	2 -> 5 [label = "SS(a)"];
	2 -> 4 [label = "S(A)"];
	5 -> 7 [label = "S(b)"];
	5 -> 5 [label = "S(a)"];
	6 -> 6 [label = "S(b)"];
	6 -> 5 [label = "S(a)"];
	7 -> 8 [label = "S(b)"];
	7 -> 5 [label = "S(a)"];
	8 -> 6 [label = "S(b)"];
	8 -> 5 [label = "S(a)"];
}
`

function Graph({ dotString, width, height }: Graph) {

	const w = width;
	const h = height || '100%'

	return (
		<GraphJs dotString={dotString} width={w} height={h} />
	);
}

Graph.defaultProps = { dotString: example, width: '100%', height: '100%' }

export default Graph;
