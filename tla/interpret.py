import json
def getobj():
    with open("log.json",'r') as f:
        return json.loads(f.read())

obj = getobj()
obj = obj[1:]

def graph(nex):
    nex = {int(k):v for k,v in nex.items()}
    one = nex[0]
    two = nex[one]
    three = nex[two]
    return f"0->{one}->{two}->{three}->E"

print(f"search for {obj[0]['state']['k']['order']}")
for state in obj:
    order = state["state"]["pc"]["order"].ljust(40)
    chaos = state["state"]["pc"]["chaos"].ljust(11)
    curr = state["state"]["curr"]["order"]
    child = state["state"]["child"]["order"]
    g = graph(state["state"]["next"])
    print(f"{order}: {chaos} : {g} : {curr} : {child}")

