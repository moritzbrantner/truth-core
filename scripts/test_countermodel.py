"""Omission-countermodel finder: solver units and rediscovery on existing results."""
import unittest

import countermodel as cm
from lean_test_support import requires_built


def atom(p, *vs):
    return {"t": "atom", "p": p, "args": [{"v": v} for v in vs]}


def forall(v, sort, body):
    return {"t": "forall", "v": v, "sort": sort, "body": body}


def imp(a, b):
    return {"t": "imp", "a": a, "b": b}


def neg(a):
    return {"t": "not", "a": a}


# PureActOperates, SelfOperatingUnmovedLives, MovedOnlyAsInPotency ⊢ PureActLives
# (TruthCore.Results.Causality.SelfOperationLife.pureActLives), written by hand.
PURE_ACT = lambda x: forall("r", "R", neg(atom("InPotency", x, "r")))  # noqa: E731
SKELETON = {
    "theorem": "Example.pureActLives",
    "carriers": ["B", "R", "T"],
    "constants": [],
    "predicates": [{"name": "InPotency", "args": ["B", "R"]}, {"name": "MovedIn", "args": ["B", "R"]},
                   {"name": "Operates", "args": ["B"]}, {"name": "LivesAt", "args": ["B", "T"]}],
    "premises": [
        {"name": "hOperates", "lean": "A", "formula": forall("x", "B", imp(PURE_ACT("x"), atom("Operates", "x")))},
        {"name": "hLife", "lean": "B", "formula": forall("x", "B", imp(atom("Operates", "x"), imp(
            forall("r", "R", neg(atom("MovedIn", "x", "r"))),
            {"t": "exists", "v": "t", "sort": "T", "body": atom("LivesAt", "x", "t")})))},
        {"name": "hMoved", "lean": "C", "formula": forall("x", "B", forall("r", "R", imp(
            atom("MovedIn", "x", "r"), atom("InPotency", "x", "r"))))},
    ],
    "conclusion": {"lean": "D", "formula": forall("x", "B", imp(PURE_ACT("x"), {
        "t": "exists", "v": "t", "sort": "T", "body": atom("LivesAt", "x", "t")}))},
    "unfolded": [],
    "module": "Example",
}


class SolverTest(unittest.TestCase):
    def test_dpll(self):
        self.assertIsNone(cm.solve([[1], [-1]], 1))
        model = cm.solve([[1, 2], [-1, 2], [-2, 3]], 3)
        self.assertTrue(model[2] and model[3])

    def test_every_omission_found_and_satisfies_its_target(self):
        for name, holds, fails in cm.omission_targets(SKELETON):
            model = cm.find_model(SKELETON, holds, fails, 2)
            self.assertIsNotNone(model, name)
            self.assertTrue(all(cm.evaluate(SKELETON, model, f) for f in holds))
            self.assertFalse(any(cm.evaluate(SKELETON, model, f) for f in fails))
            omitted = next(p for p in SKELETON["premises"] if p["name"] == name)
            self.assertFalse(cm.evaluate(SKELETON, model, omitted["formula"]))

    def test_redundant_premise_is_unresolved_not_refuted(self):
        every = forall("x", "B", atom("P", "x"))
        skeleton = {"theorem": "Example.dup", "carriers": ["B"], "constants": [],
                    "predicates": [{"name": "P", "args": ["B"]}],
                    "premises": [{"name": "h1", "lean": "A", "formula": every},
                                 {"name": "h2", "lean": "A", "formula": every}],
                    "conclusion": {"lean": "A", "formula": every}, "unfolded": [], "module": "Example"}
        reports = cm.run(skeleton, None, 2, witness=False, check=False)
        self.assertEqual([r["status"] for r in reports], ["unresolved", "unresolved"])
        self.assertIn("does not show the premise is needed", reports[0]["note"])

    def test_excluded_middle_premise_holds_in_every_model(self):
        em = forall("P", "Prop", {"t": "or", "a": atom("P"), "b": neg(atom("P"))})
        skeleton = {"theorem": "Example.em", "carriers": ["B"], "constants": [],
                    "predicates": [{"name": "Q", "args": ["B"]}],
                    "premises": [{"name": "hEM", "lean": "EM", "formula": em}],
                    "conclusion": {"lean": "C", "formula": forall("x", "B", {
                        "t": "or", "a": atom("Q", "x"), "b": neg(atom("Q", "x"))})},
                    "unfolded": [], "module": "Example"}
        [report] = cm.run(skeleton, None, 2, witness=False, check=False)
        self.assertEqual(report["status"], "unresolved")
        self.assertIn("holds in every model", report["note"])

    def test_predicate_of_predicates(self):
        # Possible (fun t => ¬ IsAt x t), with Possible : (T → Prop) → Prop.
        lam = {"lam": [{"v": "t", "sort": "T"}], "body": neg(atom("IsAt", "x", "t"))}
        possible_absent = {"t": "atom", "p": "Possible", "args": [lam]}
        skeleton = {"theorem": "Example.modal", "carriers": ["B", "T"], "constants": [],
                    "predicates": [{"name": "Possible", "args": [{"set": ["T"]}]},
                                   {"name": "IsAt", "args": ["B", "T"]}],
                    "premises": [{"name": "h", "lean": "H", "formula": forall("x", "B", possible_absent)}],
                    "conclusion": {"lean": "C", "formula": forall("x", "B", neg(possible_absent))},
                    "unfolded": [], "module": "Example"}
        model = cm.find_model(skeleton, [skeleton["premises"][0]["formula"]], [], 2)
        self.assertTrue(cm.evaluate(skeleton, model, skeleton["premises"][0]["formula"]))
        text = cm.render_model(skeleton, model)
        self.assertTrue(any(line.startswith("abbrev Possible : (T → Prop) → Prop") for line in text))

    def test_rendering_states_omission_and_negated_conclusion(self):
        name, holds, fails = next(cm.omission_targets(SKELETON, ["hLife"]))
        model = cm.find_model(SKELETON, holds, fails, 2)
        text = cm.render_certificate(SKELETON, "CM", model, name)
        self.assertIn("(A) ∧\n    ¬ (B) ∧\n    (C) ∧\n    ¬ (D)", text)
        self.assertIn("decide", text)


EXAMPLES = {
    "TruthCore.Results.Causality.SelfOperationLife.pureActLives": ["hOperates", "hLife", "hMoved"],
    "TruthCore.Results.Causality.PerfectionOfBeing.actualityOnlyInsofarAsBeing": ["hPerfect", "hBeing"],
    "TruthCore.Results.Causality.NecessaryBeingInAct.necessaryBeingInAct": ["hBridge", "hIncorruptible"],
    "TruthCore.Results.Causality.ComponentFirstness.noComponentFirst":
        ["hKinds", "hActPrior", "hNotBoth", "hParticipated", "hEfficient"],
}


@requires_built(*(t.rsplit(".", 1)[0] + ".Solution" for t in EXAMPLES))
class RediscoveryTest(unittest.TestCase):
    """The hand-written `Control.Certificate` omissions are found again and Lean accepts them."""

    def test_examples(self):
        for theorem, premises in EXAMPLES.items():
            with self.subTest(theorem=theorem):
                skeleton = cm.extract(theorem)
                self.assertEqual([p["name"] for p in skeleton["premises"]], premises)
                reports = cm.run(skeleton, None, 2, witness=True, check=True)
                self.assertEqual([r["status"] for r in reports], ["lean-checked"] * (len(premises) + 1),
                                 [r.get("lean_output") for r in reports])


if __name__ == "__main__":
    unittest.main()
