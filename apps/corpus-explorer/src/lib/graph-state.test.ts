import { describe, expect, test } from "bun:test";

import { DEFAULT_STATE, parseGraphState, serializeGraphState } from "./graph-state";

describe("graph URL state", () => {
  test("defaults to the root-path view with an empty query string", () => {
    expect(parseGraphState(new URLSearchParams())).toEqual(DEFAULT_STATE);
    expect(serializeGraphState(DEFAULT_STATE)).toBe("");
  });

  test("round-trips every filter, including tags with commas", () => {
    const query =
      "view=focus&node=STMT-A&hops=3&dir=down&q=mover&status=open&status=proved&tag=author%3AAlex+O%27Connor+%28interviewing+Destiny%2C+Steven+Bonnell+II%29&tag=stage%3A1&source=ARIST-PHYS&hide=1&sel=STMT-A&arg=ARG";
    const state = parseGraphState(new URLSearchParams(query));
    expect(state.tags).toEqual(["author:Alex O'Connor (interviewing Destiny, Steven Bonnell II)", "stage:1"]);
    expect(state.status).toEqual(["open", "proved"]);
    expect(state.hops).toBe(3);
    expect(serializeGraphState(state)).toBe(query);
  });

  test("rejects unknown values and clamps hops", () => {
    const state = parseGraphState(new URLSearchParams("view=nope&hops=99&dir=sideways&status=bogus&cluster=x"));
    expect(state.view).toBe("root");
    expect(state.hops).toBe(6);
    expect(state.dir).toBe("both");
    expect(state.status).toEqual([]);
    expect(state.cluster).toBe("passage");
  });
});
