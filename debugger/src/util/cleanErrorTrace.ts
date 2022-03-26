import _ from "lodash";

const IntegerNull = 101;
const valuesToIgnore = ["NullModelValue", "defaultInitValue", IntegerNull];

function ignore(x: any): boolean {
  return _.includes(valuesToIgnore, x);
}

interface State {
  name: string;
  no: number;
  state: any;
  id: number;
}

function flatten(states: State[]): State[] {
  return states.map((it: State) => {
    return { ...it.state, name: it.name, no: it.no };
  });
}

function toObject(a: any[]) {
  let ret: any = {};
  a.forEach((it, i: number) => {
    ret[i] = it;
  });
  return ret;
}

function removeKeysWithValuesToIgnore(o: any) {
  if (_.isArray(o)) {
    o = toObject(o);
  }
  let ret: any = {};
  for (const [k, v] of Object.entries(o)) {
    if (!ignore(v)) {
      ret[k] = v;
    }
  }
  return ret;
}

function removeKeysWithEmptyValues(o: any) {
  let ret: any = {};
  for (const [k, v] of Object.entries(o)) {
    if (Object.keys(v as Object).length !== 0) {
      ret[k] = v;
    }
  }
  return ret;
}

function specialize(o: any) {
  const cases = {
    pc: (o: any) => {
      return _.omit(o, ["initializer", "verifier"]);
    },
  };

  o.forEach((it: any) => {
    for (const [field, fun] of Object.entries(cases)) {
      it[field] = fun(it[field]);
    }
  });

  return o;
}

function initializeStates(): State[] {
  /*
  let ret = flatten(rawTrace as State[]);
  ret = ret.map((it) => _.mapValues(it, removeKeysWithValuesToIgnore));
  ret = ret.map(removeKeysWithEmptyValues);
  ret = ret.map((it, i) => {
    return { ...it, id: i };
  });

  ret = (specialize(ret) as unknown) as State[];
  return ret;
  */
 return [];
}

const states = initializeStates();

export default states;
