package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.meaning.StringsLanguage;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.flow.AWayThrough;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.ACarriedValue;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Text;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every kind of statement a condition can mean, handed to every reader that takes one into the
 * words of a row, is taken, or meets the edge of that reader's words — and never comes back as a
 * meaning this compiler did not read, unless a part of it was one.
 *
 * <p>Three readers: what a row is asked ({@link DemandReading#asked}), the column of a decision
 * a condition is ({@link DecisionMeanings#columnOf}), and whether the declarations of the input
 * prove no way through it ({@link WhatTheDeclarationsLeave#whetherRuledOut}). What none of them may
 * do is say "not read" of a statement that was read to the end: that would be a reader's shortfall passed off as
 * the reading's, and a statement read to the end is the reading's whole answer.
 *
 * <p>The partition is the fourth, and is held to the same where it reads: off the constructs a
 * body writes, each handed a condition stating one kind of statement
 * ({@link EveryStatementReadToTheEndIsDrawnOrSaidAsTheModelsTest}).
 *
 * <p>And where one of them has no words, which edge it met is one of the words that name that
 * reader's domain. A row is written at the input's positions, so where a row reader stops is a
 * fact about the input's words — a quantity on no order, an answer a row stands in. A limit of
 * what a path knows is not one of those, and coming out of a row reader it would send an author to
 * the wrong reader. Which model meets each is {@link EveryLimitOfAReadersWordsLeavesSomeModelUnreadTest}'s.
 *
 * <p>The kinds are taken from the sealed hierarchy and not from a list here, so a kind of
 * statement added without a sample below is a failure rather than a statement nobody handed to
 * these readers.
 */
class EveryPropositionIsTakenOrMeetsTheEdgeOfAReadersWordsTest {

    private static final String MODEL = """
            module m

            data Yes
            data Held = { o: Int? }
            data Node = { v: Int, below: List<Node> }

            behavior f : (n: Int, b: Bool, s: String, h: Held, xs: List<Int>, t: Node) -> Yes
            let f (n, b, s, h, xs, t) = Yes
            """;

    /** Where a row reader's words stop: the input's own words, and nothing of a path's. */
    private static final Set<WhyNotTaken.DomainLimit> A_ROWS_EDGES =
            EnumSet.allOf(WhyNotTaken.DomainLimit.class).stream()
                    .filter(each -> each.domain()
                            == WhyNotTaken.DomainLimit.Domain.WHAT_A_ROW_IS_WRITTEN_IN)
                    .collect(Collectors.toCollection(
                            () -> EnumSet.noneOf(WhyNotTaken.DomainLimit.class)));

    @Test
    void everyKindOfStatementHasASampleHere() {
        Set<Class<?>> sampled = new LinkedHashSet<>();
        samples().values().forEach(each -> sampled.add(each.getClass()));
        Set<Class<?>> kinds =
                new LinkedHashSet<>(Arrays.asList(Proposition.class.getPermittedSubclasses()));
        // What a walk carried is supposed wherever a condition is concluded whole, and handed to
        // a reader of a row it is refused (below).
        kinds.remove(Proposition.Carried.class);
        assertEquals(kinds, sampled, "a kind of statement no reader below was handed");
    }

    @Test
    void whatAWalkCarriedIsNeverAskedOfARow() {
        assertThrows(IllegalStateException.class, () -> DemandReading.asked(
                new Proposition.Carried(ACarriedValue.made(), true), reading()));
    }

    @Test
    void aStatementReadToTheEndIsNeverSaidToBeUnread() {
        InputReading read = reading();
        samples().forEach((name, stated) -> {
            if (!Proposition.stopsIn(stated).isEmpty()) {
                return;
            }
            for (boolean way : List.of(true, false)) {
                for (WhyNotTaken why : everyReaderSays(stated, way, read)) {
                    assertTrue(why instanceof WhyNotTaken.OutsideDomain,
                            () -> name + " coming out " + way + " was read to the end: " + why);
                }
            }
        });
    }

    @Test
    void whereARowReaderHasNoWordsItSaysWhichOfTheInputsWordsStopped() {
        InputReading read = reading();
        samples().forEach((name, stated) -> {
            for (boolean way : List.of(true, false)) {
                for (WhyNotTaken why : everyReaderSays(stated, way, read)) {
                    if (why instanceof WhyNotTaken.OutsideDomain(var limit)) {
                        assertTrue(A_ROWS_EDGES.contains(limit),
                                () -> name + " coming out " + way + " met " + limit
                                        + ", which is no edge of a row's words");
                    }
                }
            }
        });
    }

    /** And a statement a part of which was not read says that part, in every reader. */
    @Test
    void aPartNotReadIsSaidByEveryReader() {
        InputReading read = reading();
        Proposition unread = samples().get("unread");
        for (boolean way : List.of(true, false)) {
            assertEquals(Set.of(new WhyNotTaken.MeaningUnread(new WhyUnread.NotMetByTheReading())),
                    new LinkedHashSet<>(everyReaderSays(unread, way, read)),
                    "coming out " + way);
        }
    }

    /**
     * Some element meeting one of several things is one demand with a way for each, beside what
     * the row is asked whichever element it is — and nothing of it is left to the run.
     */
    @Test
    void someElementMeetingOneOfSeveralThingsIsOneDemandWithAWayForEach() {
        InputReading read = reading();
        Proposition element = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("xs").element()))), Rel.GT), true);
        RowDemand.ATruth beside = new RowDemand.ATruth(TermPath.of("b"), true);
        Proposition some = new Proposition.Some(new DecisionSubject.AnInput(TermPath.of("xs")),new Proposition.All(List.of(
                new Proposition.Any(List.of(element, element.denied())),
                new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("b")), true))),
                true);
        List<DemandReading.Read> asked = DemandReading.asked(some, read);
        assertTrue(asked.contains(new DemandReading.Read.Demands(beside)),
                () -> "the row is asked the truth beside the element: " + asked);
        assertTrue(asked.stream().noneMatch(DemandReading.Read.OneOf.class::isInstance),
                () -> "and no alternative of the row: " + asked);
        List<RowDemand.Exists> exists = asked.stream()
                .filter(each -> each instanceof DemandReading.Read.Demands(RowDemand.Exists _))
                .map(each -> (RowDemand.Exists) ((DemandReading.Read.Demands) each).demand())
                .toList();
        assertEquals(1, exists.size(), () -> "one element meeting one of the two: " + asked);
        List<List<RowDemand.OfAnElement>> ways = exists.getFirst().ofAnElement().ways();
        assertEquals(2, ways.size(), () -> "a way for each: " + ways);
        assertTrue(ways.stream().allMatch(way -> RowDemand.relationsAmong(way).size() == 1),
                () -> "each a relation of the element: " + ways);
        assertTrue(asked.stream().noneMatch(each -> each instanceof DemandReading.Read.Demands(
                        RowDemand.ForTheRun _)),
                () -> "and nothing of it is left to the run: " + asked);
    }

    /**
     * Every element meeting one of several things is one demand with a way for each, and not one
     * of several demands each asking every element the same: a container holding an element of
     * each kind meets it and meets neither of those.
     */
    @Test
    void everyElementMeetingOneOfSeveralThingsIsOneDemandWithAWayForEach() {
        InputReading read = reading();
        Proposition above = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("xs").element()))), Rel.GT), true);
        Proposition atMostNought = above.denied();
        // No element meets neither, which is every element meeting one of the two.
        Proposition none = new Proposition.Some(new DecisionSubject.AnInput(TermPath.of("xs")),
                new Proposition.All(List.of(above.denied(), atMostNought.denied())), false);
        List<DemandReading.Read> asked = DemandReading.asked(none, read);
        assertTrue(asked.stream().noneMatch(DemandReading.Read.OneOf.class::isInstance),
                () -> "no alternative of the row: " + asked);
        assertEquals(1, asked.size(), () -> "one demand: " + asked);
        RowDemand.ForAll every = assertInstanceOf(RowDemand.ForAll.class,
                assertInstanceOf(DemandReading.Read.Demands.class, asked.getFirst()).demand());
        assertEquals(2, every.ofEachElement().ways().size(),
                () -> "each element along one of two ways: " + every);
    }

    /** What the three readers decline {@code stated} coming out {@code way} for, together. */
    private static List<WhyNotTaken> everyReaderSays(Proposition stated, boolean way,
                                                     InputReading read) {
        Proposition asked = way ? stated : stated.denied();
        List<WhyNotTaken> out = new ArrayList<>();
        DemandReading.asked(asked, read).forEach(each -> collect(each, out));
        if (DecisionMeanings.columnOf(stated, way,
                        new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, 0),
                        Proposition::denied)
                instanceof DecidedCondition.Unread(var condition, boolean _)) {
            out.addAll(condition.whys());
        }
        if (WhatTheDeclarationsLeave.whetherRuledOut(stated, way, read)
                instanceof AWayThrough.NotRuledOut(var notAsked)) {
            out.addAll(notAsked);
        }
        return out;
    }

    private static void collect(DemandReading.Read read, List<WhyNotTaken> out) {
        switch (read) {
            case DemandReading.Read.Unread(var whys, var _) -> out.addAll(whys);
            case DemandReading.Read.OneOf oneOf -> oneOf.alternatives()
                    .forEach(each -> each.forEach(one -> collect(one, out)));
            case DemandReading.Read.Counted counted ->
                    counted.parts().forEach(one -> collect(one, out));
            case DemandReading.Read.Demands _, DemandReading.Read.Settled _,
                 DemandReading.Read.Narrows _ -> { }
        }
    }

    /** One statement of each kind, about the positions of {@link #MODEL}, each read to the end
     *  but the one that says so. */
    private static Map<String, Proposition> samples() {
        Proposition above = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atomMinusConstant(
                        new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("n"))),
                        ExactRatio.of(5)), Rel.GT), true);
        Proposition truth = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("b")),
                true);
        Proposition element = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("xs").element()))), Rel.GT), true);
        Map<String, Proposition> out = new LinkedHashMap<>();
        out.put("always", new Proposition.Always(true));
        out.put("a relation of numbers", above);
        // `s < "M"`, in the one spelling of a relation and its denial.
        Rel before = Rel.LT.orItsDenial();
        out.put("a place on an order", new Proposition.Compared(new Relation.Ordered(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("s"))),
                Text.of("M"), before), before == Rel.LT));
        out.put("a truth", truth);
        TermPath optional = TermPath.of("h").then("o");
        out.put("a case", new Proposition.InCases(new DecisionSubject.AnInput(optional),
                CasesLeft.of(Refinement.of(new Case.Presence(true))), true));
        out.put("a value being there",
                new Proposition.Present(new DecisionSubject.AnInput(optional), true));
        out.put("a string in a language", new Proposition.InTheStrings(
                new Proposition.InTheStrings.Strings.AtAPosition(TermPath.of("s")),
                new StringsLanguage(PatternMeaning.text("ab")), true));
        out.put("two values being one", new Proposition.SameValue(
                new DecisionSubject.AnInput(TermPath.of("n")),
                new DecisionSubject.AnInput(TermPath.of("s")), true));
        out.put("the last of its value", new Proposition.LastToHold(
                new DecisionSubject.AnInput(TermPath.of("xs")),
                new DecisionSubject.AnInput(TermPath.of("xs").element()), true));
        out.put("where an operation answers", new Proposition.WhereItAnswers(truth, above));
        out.put("both", new Proposition.All(List.of(above, truth)));
        out.put("either", new Proposition.Any(List.of(above, truth)));
        out.put("some element", new Proposition.Some(new DecisionSubject.AnInput(TermPath.of("xs")), element, true));
        out.put("on some application", new Proposition.OnAnApplication(List.of(above, truth)));
        out.put("so many of them holding", new Proposition.SoManyHold(Stream.of(above, truth)
                .sorted(Comparator.comparing(Proposition::key)).toList(), List.of(1, 1),
                List.of(1)));
        TermPath node = TermPath.of("t");
        out.put("some node a search reaches", new Proposition.SomeReachable(node, node,
                List.of("below"), new Proposition.Compared(new Relation.Affine(
                        LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(
                                new NumericTerm.ValueOf(node.then("v")))), Rel.GT), true),
                Optional.empty(), true));
        out.put("unread", new Proposition.Unread(Optional.empty(), 0,
                new WhyUnread.NotMetByTheReading(), false, true));
        return out;
    }

    private static InputReading reading() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertTrue(!compilation.modules().isEmpty(), () -> "the model under test compiles: "
                + compilation.diagnostics().values().stream().flatMap(List::stream)
                        .map(each -> each.diagnostic().code()).toList());
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        var inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(rules);
    }
}
