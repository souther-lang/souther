package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclarationReadings;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.SettledWork;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.KnownExtents;
import souther.compiler.values.StringMachineAnswers;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules about a position's strings offer is worked out once for a whole generation,
 * however many times the search asks for the position's values.
 *
 * <p>The value a pattern offers a row, what several rules met together offer, and what that offer
 * was short of are each settled by the rules. The search asks for a position's values from each
 * settling of the positions around it, so a model whose other position divides into several classes
 * has this one asked about from each of them — and what changes from one asking to the next is where
 * the search is, which is nothing the machines depend on.
 *
 * <p>Counted rather than timed: what is held is how many times the work was done, which is a shape
 * and not a speed. Each kind is held to the number of different pieces of it the generation asked
 * for, read off the asking itself, and each has a control showing that the search asks for the same
 * piece more than once.
 */
class APatternIsCompiledOnceHoweverOftenASearchAsksForItsPositionTest {

    /** A format on one position, and another position that divides into three. */
    private static final String A_FORMAT = """
            module example.codes

            data Code = String
                invariant format = String.matches("T[0-9]{3}", value)

            data Grade = Low | Middle | High

            data Ok

            behavior grade : (g: Grade, code: Code) -> Ok

            let grade (g, code) = Ok
            """;

    /** The same with a count beside the format, which is two rules about the strings to meet. */
    private static final String A_FORMAT_AND_A_COUNT = A_FORMAT.replace(
            "invariant format = String.matches(\"T[0-9]{3}\", value)",
            "invariant format = String.matches(\"T[0-9]{3}\", value)\n"
                    + "    invariant counted = String.length(value) >= 4");

    /** A set of formatted strings that holds several, which is filled with values that differ. */
    private static final String A_SET_OF_THEM = """
            module example.codes

            data Code = String
                invariant format = String.matches("T[0-9]{3}", value)

            data Codes = Set<Code>
                invariant several = Set.size(value) >= 2

            data Grade = Low | Middle | High

            data Ok

            behavior grade : (g: Grade, codes: Codes) -> Ok

            let grade (g, codes) = Ok
            """;

    /**
     * The format and the position that divides, as two fields of one value.
     *
     * <p>What a search that came back empty says it was short of is read at the positions of the
     * value it was composing, so the format has to be one of them.
     */
    private static final String A_FORMAT_IN_ONE_VALUE = """
            module example.codes

            data Code = String
                invariant format = String.matches("T[0-9]{3}", value)

            data Grade = Low | Middle | High

            data Ticket = { g: Grade, code: Code }

            data Ok

            behavior grade : (t: Ticket) -> Ok

            let grade (t) = Ok
            """;

    @Test
    void aGenerationCompilesThePatternOnce() {
        Asked asked = new Asked();
        MeasuredInput subject = subjectOf(A_FORMAT, asked);

        long before = SettledWork.timesDone(Partitions.PatternWitness.class);
        FillResult filled = fill(subject, Generator.CandidateCheck.ANY);

        assertFalse(filled.rows().isEmpty(), "the generation wrote rows");
        assertEquals(1, asked.of(Partitions.PatternWitness.class), "one pattern was asked about");
        assertEquals(1, SettledWork.timesDone(Partitions.PatternWitness.class) - before,
                "and compiled for the first asking and lent to every other");
    }

    @Test
    void aSecondGenerationInTheSameRevisionCompilesNothing() {
        MeasuredInput subject = subjectOf(A_FORMAT, new Asked());
        fill(subject, Generator.CandidateCheck.ANY);

        long before = SettledWork.timesDone(Partitions.PatternWitness.class);
        fill(subject, Generator.CandidateCheck.ANY);

        assertEquals(0, SettledWork.timesDone(Partitions.PatternWitness.class) - before,
                "the revision already knows what the format offers");
    }

    @Test
    void whatTwoRulesOfferTogetherIsWorkedOutOncePerQuestion() {
        heldToWhatWasAsked(A_FORMAT_AND_A_COUNT, Generator.CandidateCheck.ANY,
                Partitions.StringsTheRulesAdmit.class);
    }

    /** The same for the values a set of them is filled from, which have to differ. */
    @Test
    void whatASetIsFilledFromIsWorkedOutOncePerQuestion() {
        heldToWhatWasAsked(A_SET_OF_THEM, Generator.CandidateCheck.ANY,
                Partitions.StringsTheRulesAdmit.class);
    }

    /**
     * What the offer was short of is asked wherever a search came back without a row, which a
     * check refusing everything makes every combination.
     */
    @Test
    void whatTheOfferWasShortOfIsWorkedOutOncePerQuestion() {
        heldToWhatWasAsked(A_FORMAT_IN_ONE_VALUE, (_, _) ->
                        new Generator.CandidateCheck.Built.Refused("the model refuses it"),
                Partitions.WhatTheOfferIsShortOf.class);
    }

    /**
     * The negative control for the first: with nothing to keep the witness, the search asks for the
     * position more than once.
     *
     * <p>Without it, the count of one above would say as much about a search that asked once as
     * about a revision that kept what it was told.
     */
    @Test
    void withNothingToKeepItTheSearchCompilesThePatternAtEveryAsking() {
        assertTrue(doneUnshared(A_FORMAT, Generator.CandidateCheck.ANY,
                        Partitions.PatternWitness.class) > 1,
                "the search asks for the position from more than one place, so a reading that keeps"
                        + " nothing compiles the format more than once");
    }

    /**
     * {@code kind} done once for each different piece of it the generation asked for, with a
     * control showing the same piece asked for again.
     */
    private static void heldToWhatWasAsked(String model, Generator.CandidateCheck check,
                                           Class<?> kind) {
        Asked asked = new Asked();
        MeasuredInput subject = subjectOf(model, asked);
        long before = SettledWork.timesDone(kind);
        fill(subject, check);
        long done = SettledWork.timesDone(kind) - before;

        assertTrue(asked.of(kind) > 0, "the generation asked for this work at all");
        assertEquals(asked.of(kind), done,
                "each different piece of work was done for its first asking and lent to the rest");
        assertTrue(doneUnshared(model, check, kind) > done,
                "and the search asks for the same piece more than once, so a reading that keeps"
                        + " nothing does more of it");
    }

    private static long doneUnshared(String model, Generator.CandidateCheck check, Class<?> kind) {
        MeasuredInput subject = subjectOf(model, null);
        long before = SettledWork.timesDone(kind);
        fill(subject, check);
        return SettledWork.timesDone(kind) - before;
    }

    private static FillResult fill(MeasuredInput subject, Generator.CandidateCheck check) {
        return GenerationFixtures.fill(subject, List.of(), check, Budgets.generation());
    }

    /**
     * The input of {@code grade}, read in the compilation's own world with what is asked of it
     * recorded in {@code asked}, or in one that keeps nothing where {@code asked} is null.
     */
    private static MeasuredInput subjectOf(String model, Asked asked) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        assertNotNull(sigs, "the model did not compile");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext world = asked == null
                ? RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)
                : RuleReadingContext.of(rules, ReadAs.THE_COMPILATION_DOES,
                        asked.over(compilation.db().readings()));
        InputDomain domain = InputDomain.of(sigs.get("grade"), world);
        Partitions.Partitioning partitioning =
                Partitions.of("grade", domain, rules, ReadAs.THE_COMPILATION_DOES);
        return MeasuredInput.of("grade", domain.reading(rules), partitioning);
    }

    /** The different pieces of settled work a reading asked its lender for. */
    private static final class Asked {

        private final Set<SettledWork<?>> seen = new HashSet<>();

        long of(Class<?> kind) {
            return seen.stream().filter(kind::isInstance).count();
        }

        /**
         * {@code lender}, with every piece of settled work asked of it written down here.
         *
         * <p>Its canonical readings are not lent through this: what a reading is handed is a type
         * of the reading's own package. A reading asked here reads the declaration itself, which
         * changes what it costs and not what any settled work is asked.
         */
        DeclarationReadings over(DeclarationReadings lender) {
            return new DeclarationReadings() {

                @Override
                public StringMachineAnswers of(TypeKey declaration) {
                    return lender.of(declaration);
                }

                @Override
                public KnownExtents extents() {
                    return lender.extents();
                }

                @Override
                public <A> A settled(SettledWork<A> work) {
                    seen.add(work);
                    return lender.settled(work);
                }

                @Override
                public TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule declaration) {
                    return lender.ownerOf(declaration);
                }
            };
        }
    }
}
