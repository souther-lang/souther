package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a fork's answer turns on is read in the names that stand where it is written.
 *
 * <p>A helper expanded inside a closure binds its parameters inside the closure, and a rule in its
 * body is about what those parameters were handed. In the names the fork stands in, a field of the
 * helper's parameter is no position at all, and a fork read there is a rule about a value made from
 * the input. Written with the helper or without it, a model says the same thing, so each spelling
 * here is held to the one that writes the rule out where the fork is.
 */
class WhatAForkTurnsOnIsReadWhereItIsWrittenTest {

    /** A truth a helper reads off its parameter, inside a closure. */
    @Test
    void aTruthAHelperReadsInsideAClosureIsThePositionItReads() {
        assertTheSameAs("""
                let abroadOf (t: Trip): Bool = t.abroad
                let submit (t) = if List.any(r -> abroadOf(t), [High]) then 2 else 1
                """, """
                let submit (t) = if List.any(r -> t.abroad, [High]) then 2 else 1
                """);
    }

    /** A comparison and a truth the helper joins, each read where it is. */
    @Test
    void aHelperJoiningAComparisonAndATruthIsReadPartByPart() {
        assertTheSameAs("""
                let either (t: Trip): Bool = t.cost >= 100 || t.abroad
                let submit (t) = if List.any(r -> either(t), [High]) then 2 else 1
                """, """
                let submit (t) = if List.any(r -> t.cost >= 100 || t.abroad, [High]) then 2 else 1
                """);
    }

    /** A helper choosing by the element it is handed, which is one of the values written out. */
    @Test
    void aHelperMatchingTheElementItIsHandedIsReadArmByArm() {
        assertTheSameAs("""
                let applies (t: Trip, r: Reason): Bool =
                    match r with
                        | High -> t.cost >= 100
                        | Abroad -> t.abroad
                let submit (t) = if List.any(r -> applies(t, r), [High, Abroad]) then 2 else 1
                """, """
                let submit (t) =
                    if List.any(r -> match r with
                            | High -> t.cost >= 100
                            | Abroad -> t.abroad, [High, Abroad]) then 2 else 1
                """);
    }

    /**
     * A name an arm binds is the position the arm narrowed, wherever the arm is read from.
     *
     * <p>Without a closure as well, because a fork on a {@code match} is walked into the arm the
     * same way: in the names outside the arm, the arm's name stands for nothing.
     */
    @Test
    void aNameAnArmBindsIsWhatTheArmNarrowed() {
        String kinds = """
                data Urgent = { flag: Bool }
                data Normal
                data Kind = Urgent | Normal
                data Order = { kind: Kind }

                behavior ship : (o: Order) -> Int
                """;
        String arm = """
                match o.kind with
                    | Urgent as u -> u.flag
                    | Normal -> false""";
        PartitionEvidence direct = measured(kinds + "let ship (o) = if (" + arm + ") then 2 else 1",
                "ship");
        PartitionEvidence closure = measured(kinds
                + "let ship (o) = if List.any(r -> " + arm + ", [1]) then 2 else 1", "ship");
        assertEquals(List.of(), direct.notRead(), "the arm's name is read in a fork on the match");
        assertEquals(List.of(), closure.notRead(), "and in a closure the fork turns on");
        assertEquals(toldApart(direct), toldApart(closure));
    }

    /**
     * Which answers a predicate in a helper can give is read where the helper binds its parameter.
     *
     * <p>{@code t.cost <= t.cost + 1} holds on every row, so the closure always holds and the fork
     * turns on {@code t.abroad} alone. In the names outside the helper its two sides are about
     * nothing, so the closure may come out either way, and a row whose way past it is the other way
     * is a row this reading cannot account for.
     */
    @Test
    void aPredicateAHelperSettlesIsSettledInsideAClosure() {
        String rows = """

                example submit
                    | "home" : (Trip { cost = 1, abroad = false }) -> 1
                    | "abroad" : (Trip { cost = 1, abroad = true }) -> 2
                """;
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, verdictOf("""
                let submit (t) =
                    if List.any(r -> t.cost <= t.cost + 1, [High]) && t.abroad then 2 else 1
                """ + rows), "written out where the fork is");
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, verdictOf("""
                let always (t: Trip): Bool = t.cost <= t.cost + 1
                let submit (t) =
                    if List.any(r -> always(t), [High]) && t.abroad then 2 else 1
                """ + rows), "and written in a helper");
    }

    private static AdequacyReport.AdequacyStatus verdictOf(String body) {
        Compilation compilation = compiled("""
                data Trip = { cost: Int, abroad: Bool }
                data Reason = High | Abroad

                behavior submit : (t: Trip) -> Int
                """ + body);
        assertEquals(List.of(), compilation.errors(), "the rows are the model's answers");
        return AdequacyReport.of(compilation).adequacy();
    }

    /**
     * Each spelling reads every rule, and tells apart at each position what the written-out one
     * does.
     *
     * <p>Both halves, because the written-out spelling leaving nothing unread is what makes the
     * comparison say anything: a model the reading gave up on in both spellings would agree.
     */
    private static void assertTheSameAs(String helper, String written) {
        PartitionEvidence through = measured(helper);
        PartitionEvidence direct = measured(written);
        assertEquals(List.of(), direct.notRead(), "the rule written out where the fork is is read");
        assertEquals(List.of(), through.notRead(), "and the same rule written in a helper");
        assertEquals(toldApart(direct), toldApart(through));
    }

    private static List<String> toldApart(PartitionEvidence evidence) {
        return evidence.axes().stream()
                .map(axis -> axis.classes() + " " + axis.toldApart()).toList();
    }

    private static PartitionEvidence measured(String body) {
        return measured("""
                data Trip = { cost: Int, abroad: Bool }
                data Reason = High | Abroad

                behavior submit : (t: Trip) -> Int
                """ + body, "submit");
    }

    private static PartitionEvidence measured(String model, String behavior) {
        Compilation compilation = compiled(model);
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + compilation.errors());
        return coverage.get(behavior);
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
