package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.flow.AWayThrough;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
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
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every kind of statement a condition can mean, handed to every reader that takes one into the
 * words of a row, is taken, or meets the edge of that reader's words — and never comes back as a
 * meaning this compiler did not read, unless a part of it was one.
 *
 * <p>Three readers: what a row is asked ({@link DemandReading#asked}), the column of a decision
 * a condition is ({@link DecisionMeanings#columnOf}), and whether the rules of the input leave a
 * way through it ({@link WhatTheRulesLeave#admits}). What none of them may do is say "not read"
 * of a statement that was read to the end: that would be a reader's shortfall passed off as the
 * reading's, and a statement read to the end is the reading's whole answer.
 *
 * <p>And where one of them has no words, which edge it met is one of the words that name that
 * reader's domain. A row is written at the input's positions, so where a row reader stops is a
 * fact about the input's words — a quantity on no order, a size nothing measures, a position the
 * reading holds no place for, an answer a row stands in. A limit of what a path knows is not
 * one of those, and coming out of a row reader it would send an author to the wrong reader.
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

            behavior f : (n: Int, b: Bool, s: String, h: Held, xs: List<Int>) -> Yes
            let f (n, b, s, h, xs) = Yes
            """;

    /** Where a row reader's words stop: the input's own words, and nothing of a path's. */
    private static final Set<WhyNotTaken.DomainLimit> A_ROWS_EDGES = EnumSet.of(
            WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER,
            WhyNotTaken.DomainLimit.A_SIZE_NOTHING_MEASURES,
            WhyNotTaken.DomainLimit.A_POSITION_THE_READING_HOLDS_NO_PLACE_FOR,
            WhyNotTaken.DomainLimit.AN_ANSWER_A_ROW_STANDS_IN);

    @Test
    void everyKindOfStatementHasASampleHere() {
        Set<Class<?>> sampled = new LinkedHashSet<>();
        samples().values().forEach(each -> sampled.add(each.getClass()));
        assertEquals(new LinkedHashSet<>(Arrays.asList(Proposition.class.getPermittedSubclasses())),
                sampled, "a kind of statement no reader below was handed");
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

    /** What the three readers decline {@code stated} coming out {@code way} for, together. */
    private static List<WhyNotTaken> everyReaderSays(Proposition stated, boolean way,
                                                     InputReading read) {
        Proposition asked = way ? stated : stated.denied();
        List<WhyNotTaken> out = new ArrayList<>();
        DemandReading.asked(asked, read).forEach(each -> collect(each, out));
        if (DecisionMeanings.columnOf(stated, way, new ConditionOccurrence("f", 0))
                instanceof DecidedCondition.Unread(var condition, boolean _)) {
            out.addAll(condition.whys());
        }
        if (WhatTheRulesLeave.admits(stated, way, read)
                instanceof AWayThrough.NotRuledOut(var notAsked)) {
            out.addAll(notAsked);
        }
        return out;
    }

    private static void collect(DemandReading.Read read, List<WhyNotTaken> out) {
        switch (read) {
            case DemandReading.Read.Unread(var whys) -> out.addAll(whys);
            case DemandReading.Read.OneOf(var alternatives) ->
                    alternatives.forEach(each -> each.forEach(one -> collect(one, out)));
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
        out.put("two values being one", new Proposition.SameValue(
                new DecisionSubject.AnInput(TermPath.of("n")),
                new DecisionSubject.AnInput(TermPath.of("s")), true));
        out.put("both", new Proposition.All(List.of(above, truth)));
        out.put("either", new Proposition.Any(List.of(above, truth)));
        out.put("some element", new Proposition.Some(TermPath.of("xs"), element, true));
        out.put("on some application", new Proposition.OnAnApplication(List.of(above, truth)));
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
