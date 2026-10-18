package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a helper that calls itself answers is read by induction over what it walks, and is read only
 * where the induction is shown: a walk of a list by its head, or a search from a node whose every
 * call is on a node below, whose body one step down says what the search from the node does. Where
 * that is not shown — a call back on the same node, the other quantifier over the nodes below, a
 * value that stays put standing under the node, a recursion through two helpers — the answer is not
 * read, and nothing is made up for it.
 */
class WhatARecursiveHelperAnswersIsReadByInductionTest {

    private static final String DECLARATIONS = """
            module demo

            data Node = { v: Int, below: List<Node> }
            data In = { xs: List<Int>, ys: List<Int>, t: Node, w: Int }
            """;

    private static final TermPath T = TermPath.of("i").then("t");

    @Test
    void aWalkOfAListByItsHeadIsSomeElementMeetingWhatItsStepAsks() {
        Proposition stated = stated("""
                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if x > 0 then [ x ] else go(List.drop(1, xs))
                """, "Bool.not(List.isEmpty(go(i.xs)))");
        Proposition.Some some = assertInstanceOf(Proposition.Some.class, stated);
        assertEquals(new DecisionSubject.AnInput(TermPath.of("i").then("xs")), some.container());
        assertTrue(some.holds());
    }

    @Test
    void aWalkOfAListReorderedIsSomeElementMeetingWhatItsStepAsksOfTheListItWasReorderedFrom() {
        Proposition stated = stated("""
                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if x > 0 then [ x ] else go(List.drop(1, xs))
                """, "Bool.not(List.isEmpty(go(List.reverse(i.xs))))");
        Proposition.Some some = assertInstanceOf(Proposition.Some.class, stated);
        assertEquals(new DecisionSubject.AnInput(TermPath.of("i").then("xs")), some.container());
        assertTrue(some.holds());
    }

    @Test
    void aWalkOfAListReorderedWhoseAnswerTurnsOnTheLastElementIsNotRead() {
        Proposition stated = stated("""
                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if List.isEmpty(List.drop(1, xs)) then (if x > 0 then [ x ] else [])
                                    else go(List.drop(1, xs))
                """, "Bool.not(List.isEmpty(go(List.reverse(i.xs))))");
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    @Test
    void aWalkOfAListThatKeptSomeOfTheElementsIsNotSomeElementOfTheListItWasMadeFrom() {
        Proposition stated = stated("""
                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if x > 0 then [ x ] else go(List.drop(1, xs))
                """, "Bool.not(List.isEmpty(go(List.filter(x -> x < 9, i.xs))))");
        assertFalse(stated instanceof Proposition.Some some
                && new DecisionSubject.AnInput(TermPath.of("i").then("xs"))
                        .equals(some.container()),
                () -> "read as " + stated);
    }

    @Test
    void aWalkWhoseAnswerTurnsOnTheLastElementIsNotRead() {
        Proposition stated = stated("""
                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if List.isEmpty(List.drop(1, xs)) then (if x > 0 then [ x ] else [])
                                    else go(List.drop(1, xs))
                """, "Bool.not(List.isEmpty(go(i.xs)))");
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    @Test
    void whatAWalkCarriedAskedInsideAClosureOfItsStepIsTheSameForEveryElementThere() {
        // The step reads what it carried inside a closure over another list: read once with that
        // standing as itself, it is no part of any one element there, and concluded either way
        // the closure's container holding anything is what is left of it.
        Proposition stated = stated("", """
                Bool.not(List.isEmpty(List.fold((found, x) ->
                    if List.isEmpty(found)
                        then (if List.any(y -> y > x || Bool.not(List.isEmpty(found)), i.ys)
                              then [ x ] else [])
                        else found,
                    [], i.xs)))""");
        assertFalse(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
        assertInstanceOf(Proposition.Some.class, stated);
    }

    @Test
    void aSearchForSomeNodeIsSomeReachableNodeMeetingWhatTheNodeIsAsked() {
        Proposition.SomeReachable reached = assertInstanceOf(Proposition.SomeReachable.class,
                stated("""
                        let reaches (node: Node, w: Int): Bool =
                            node.v > w || List.any(c -> reaches(c, w), node.below)
                        """, "reaches(i.t, i.w)"));
        assertTrue(reached.holds());
        assertEquals(T, reached.at());
        assertEquals(T, reached.writtenAt());
        assertEquals(List.of("below"), reached.through());
        assertInstanceOf(Proposition.Compared.class, reached.atANode());
        // The node meeting it settles that some node does; the node failing it and having nothing
        // below settles that none does.
        assertEquals(reached.atANode(), reached.surely(true));
        Proposition.All none = assertInstanceOf(Proposition.All.class, reached.surely(false));
        assertTrue(none.parts().contains(reached.atANode().denied()), () -> "read as " + none);
    }

    @Test
    void aSearchWhoseNodesMustEachMeetSomethingIsNoNodeFailingIt() {
        Proposition.SomeReachable reached = assertInstanceOf(Proposition.SomeReachable.class,
                stated("""
                        let fits (node: Node, w: Int): Bool =
                            node.v > w && List.all(c -> fits(c, w), node.below)
                        """, "fits(i.t, i.w)"));
        assertFalse(reached.holds());
        assertInstanceOf(Proposition.Compared.class, reached.atANode());
        // Every node fitting is settled by the node fitting and having nothing below, and its
        // failing by the node failing.
        assertEquals(reached.atANode(), reached.surely(false));
        assertInstanceOf(Proposition.All.class, reached.surely(true));
    }

    @Test
    void aSearchFoldedOverTheNodesBelowIsReadTheSameWay() {
        Proposition.SomeReachable reached = assertInstanceOf(Proposition.SomeReachable.class,
                stated("""
                        let pathTo (node: Node, w: Int): List<Int> =
                            if node.v == w
                                then [ node.v ]
                                else {
                                    let below = List.fold((found, r) ->
                                            if List.isEmpty(found) then pathTo(r, w) else found,
                                        [], node.below)
                                    if List.isEmpty(below) then [] else [ node.v ] ++ below
                                }
                        """, "Bool.not(List.isEmpty(pathTo(i.t, i.w)))"));
        assertTrue(reached.holds());
        assertEquals(List.of("below"), reached.through());
    }

    @Test
    void someNodeBelowIsNeverTakenForEveryNodeBelow() {
        // The node meeting it or every node below doing so: one step down it states every node
        // below, and a search states some node below, so the two are not one.
        Proposition stated = stated("""
                let odd (node: Node, w: Int): Bool =
                    node.v > w || List.all(c -> odd(c, w), node.below)
                """, "odd(i.t, i.w)");
        assertFalse(stated instanceof Proposition.SomeReachable, () -> "read as " + stated);
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    @Test
    void aCallOnTheSameNodeIsNoSearch() {
        Proposition stated = stated("""
                partial let stuck (node: Node, w: Int): Bool =
                    node.v > w || List.any(c -> stuck(node, w), node.below)
                """, "stuck(i.t, i.w)");
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    @Test
    void aValueThatStaysPutUnderTheNodeIsNoSearch() {
        // `w` is the node's own value at the top and the top's value further down: moving the node
        // would move what it is compared with.
        Proposition stated = stated("""
                let reaches (node: Node, w: Int): Bool =
                    node.v > w || List.any(c -> reaches(c, w), node.below)
                """, "reaches(i.t, i.t.v)");
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    @Test
    void aRecursionThroughTwoHelpersIsReadAsNeither() {
        Proposition stated = stated("""
                let up (node: Node, w: Int): Bool =
                    node.v > w || List.any(c -> down(c, w), node.below)
                        || List.any(c -> up(c, w), node.below)
                let down (node: Node, w: Int): Bool =
                    node.v < w || List.any(c -> up(c, w), node.below)
                        || List.any(c -> down(c, w), node.below)
                """, "up(i.t, i.w)");
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    /** What the condition of {@code f}'s one fork states, with {@code lets} declared beside it. */
    private static Proposition stated(String lets, String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + lets + """

                behavior f : (i: In) -> Int
                let f (i) =
                    if (%s) then 1 else 0
                """.formatted(condition), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), () -> "compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()));
        return Pullback.ofATruth(fork.cond(), reads, read, Optional.empty()).proposition();
    }
}
