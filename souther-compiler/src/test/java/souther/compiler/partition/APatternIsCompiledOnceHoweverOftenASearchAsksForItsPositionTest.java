package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclarationReadings;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.regex.PatternPlan;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.StringMachineAnswers;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern is compiled once for a whole generation, however many times and from however many
 * questions the search asks for the position it is on.
 *
 * <p>The search asks for a position's values from each settling of the positions around it, and
 * three questions are asked there: the value one rule offers, what the rules meet in, and what the
 * offer was short of. Each of them is made out of the machines of the patterns, and a pattern's
 * machine is settled by the pattern — so it is built once, by its producer, and every question
 * borrows it.
 *
 * <p>Counted where the machines are built ({@link PatternPlan#compilationsMade}), which is the
 * expensive thing, and not where the questions are answered: a question answered once can still
 * build a machine another question built already.
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

    private static final Generator.CandidateCheck REFUSING_EVERYTHING =
            (_, _) -> new Generator.CandidateCheck.Built.Refused("the model refuses it");

    /** Each model with the check its search is run under. */
    private static Map<String, Generator.CandidateCheck> models() {
        Map<String, Generator.CandidateCheck> out = new LinkedHashMap<>();
        out.put(A_FORMAT, Generator.CandidateCheck.ANY);
        out.put(A_FORMAT_AND_A_COUNT, Generator.CandidateCheck.ANY);
        out.put(A_SET_OF_THEM, Generator.CandidateCheck.ANY);
        out.put(A_FORMAT_IN_ONE_VALUE, REFUSING_EVERYTHING);
        return out;
    }

    /**
     * How many machines each model's generation builds: the format, and where a count is written,
     * the strings of each length a question lays over it.
     *
     * <p>Worked out from the model and not read off a run. The format is built once by its
     * producer and borrowed by every question. The count beside it is met at every length from four
     * up, by what the rules offer together, and at exactly four, by a value of the length the count
     * asks for — two questions, each worked out once, each building its own strings of that length.
     */
    private static final Map<String, Integer> MACHINES_BUILT = Map.of(
            A_FORMAT, 1,
            A_FORMAT_AND_A_COUNT, 3,
            A_SET_OF_THEM, 1,
            A_FORMAT_IN_ONE_VALUE, 1);

    /** How many patterns the rules of each model state, which is how many machines a producer
     *  builds. */
    private static final Map<String, Integer> PATTERNS_STATED = Map.of(
            A_FORMAT, 1,
            A_FORMAT_AND_A_COUNT, 1,
            A_SET_OF_THEM, 1,
            A_FORMAT_IN_ONE_VALUE, 1);

    /**
     * Each pattern a rule states is built once, by its producer, whichever questions met it and
     * however often the search asked them.
     *
     * <p>Met by more than one question in the model with a count: offered on its own, met with the
     * strings of four or more characters, and met with the strings of exactly four.
     */
    @Test
    void eachPatternARuleStatesIsBuiltOnceByItsProducer() {
        models().forEach((model, check) -> {
            MeasuredInput subject = subjectOf(model, null);

            long before = RevisionKnowledge.timesDone(Partitions.PatternForAWitness.class);
            fill(subject, check);

            assertEquals(PATTERNS_STATED.get(model).longValue(),
                    RevisionKnowledge.timesDone(Partitions.PatternForAWitness.class) - before,
                    "one producer per pattern a rule states: " + model);
        });
    }

    /**
     * And every machine the generation builds is accounted for: the patterns, once each, and the
     * strings so many characters long each question builds for itself, once each since the
     * question is worked out once.
     */
    @Test
    void everyMachineAGenerationBuildsIsAPatternOnceOrAQuestionsOwnOnce() {
        models().forEach((model, check) -> {
            MeasuredInput subject = subjectOf(model, null);

            long before = PatternPlan.compilationsMade();
            fill(subject, check);

            assertEquals(MACHINES_BUILT.get(model).longValue(),
                    PatternPlan.compilationsMade() - before,
                    "each pattern built once and lent, and each question's own machine built"
                            + " for the one time the question is worked out: " + model);
        });
    }

    @Test
    void aSecondGenerationInTheSameRevisionCompilesNothing() {
        models().forEach((model, check) -> {
            MeasuredInput subject = subjectOf(model, null);
            fill(subject, check);

            long before = PatternPlan.compilationsMade();
            fill(subject, check);

            assertEquals(0, PatternPlan.compilationsMade() - before,
                    "the revision already holds every machine: " + model);
        });
    }

    /**
     * The negative control: with nothing to keep the machines, the search builds them again.
     *
     * <p>Without it, the counts above would say as much about a search that asked once as about a
     * revision that kept what it was told.
     */
    @Test
    void withNothingToKeepThemTheSearchBuildsThePatternsAgain() {
        models().forEach((model, check) -> {
            MeasuredInput shared = subjectOf(model, null);
            long before = PatternPlan.compilationsMade();
            fill(shared, check);
            long kept = PatternPlan.compilationsMade() - before;

            MeasuredInput unshared = subjectOf(model, NOTHING_KEPT);
            before = PatternPlan.compilationsMade();
            fill(unshared, check);

            assertTrue(PatternPlan.compilationsMade() - before > kept,
                    "the search asks about the position from more than one place, so a reading"
                            + " that keeps nothing builds more: " + model);
        });
    }

    /** What several rules meet in is worked out once for each different question. */
    @Test
    void whatTheRulesOfferTogetherIsWorkedOutOncePerQuestion() {
        heldToWhatWasAsked(A_FORMAT_AND_A_COUNT, Generator.CandidateCheck.ANY,
                Partitions.StringsTheRulesAdmit.class);
        heldToWhatWasAsked(A_SET_OF_THEM, Generator.CandidateCheck.ANY,
                Partitions.StringsTheRulesAdmit.class);
    }

    /**
     * What the offer was short of is asked wherever a search came back without a row, which a
     * check refusing everything makes every combination.
     */
    @Test
    void whatTheOfferWasShortOfIsWorkedOutOncePerQuestion() {
        heldToWhatWasAsked(A_FORMAT_IN_ONE_VALUE, REFUSING_EVERYTHING,
                Partitions.WhatTheOfferIsShortOf.class);
    }

    /** {@code kind} done once for each different piece of it the generation asked for. */
    private static void heldToWhatWasAsked(String model, Generator.CandidateCheck check,
                                           Class<?> kind) {
        Asked asked = new Asked();
        MeasuredInput subject = subjectOf(model, asked);
        long before = RevisionKnowledge.timesDone(kind);
        fill(subject, check);

        assertTrue(asked.of(kind) > 0, "the generation asked for this work at all");
        assertEquals(asked.of(kind), RevisionKnowledge.timesDone(kind) - before,
                "each different piece of work was done for its first asking and lent to the rest");
    }

    private static FillResult fill(MeasuredInput subject, Generator.CandidateCheck check) {
        return GenerationFixtures.fill(subject, List.of(), check, Budgets.generation());
    }

    /** A world that keeps nothing, for the control. */
    private static final Asked NOTHING_KEPT = new Asked();

    /**
     * The input of {@code grade}: read in the compilation's own world, with what is asked of it
     * recorded where {@code asked} is given, or in one that keeps nothing where it is
     * {@link #NOTHING_KEPT}.
     */
    private static MeasuredInput subjectOf(String model, Asked asked) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        assertNotNull(sigs, "the model did not compile");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext world = asked == NOTHING_KEPT
                ? RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)
                : RuleReadingContext.of(rules, ReadAs.THE_COMPILATION_DOES, asked == null
                        ? compilation.db().readings() : asked.over(compilation.db().readings()));
        InputDomain domain = InputDomain.of(sigs.get("grade"), world);
        Partitions.Partitioning partitioning =
                Partitions.of("grade", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        return MeasuredInput.of("grade", domain.reading(rules), partitioning);
    }

    /** The different pieces of work a reading asked the revision for. */
    private static final class Asked {

        private final Set<RevisionWork<?>> seen = new HashSet<>();

        long of(Class<?> kind) {
            return seen.stream().filter(kind::isInstance).count();
        }

        /**
         * {@code lender}, with every piece of work a reading asks its revision for written down
         * here.
         *
         * <p>Its canonical readings are not lent through this: what a reading is handed is a type
         * of the reading's own package. A reading asked here reads the declaration itself, which
         * changes what it costs and not what work is asked.
         */
        DeclarationReadings over(DeclarationReadings lender) {
            RevisionKnowledge recording = new RevisionKnowledge() {

                @Override
                public <A> A settled(RevisionWork<A> work) {
                    seen.add(work);
                    return lender.revision().settled(work);
                }
            };
            return new DeclarationReadings() {

                @Override
                public StringMachineAnswers of(TypeKey declaration) {
                    return lender.of(declaration);
                }

                @Override
                public RevisionKnowledge revision() {
                    return recording;
                }

                @Override
                public TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule declaration) {
                    return lender.ownerOf(declaration);
                }
            };
        }
    }
}
