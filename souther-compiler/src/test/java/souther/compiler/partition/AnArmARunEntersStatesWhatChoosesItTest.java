package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ClauseName;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.WrittenOwner;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run entering an arm of a fork that chooses by no condition states: an attempt's arms by the
 * clauses of the invariant it checks, and a {@code match}'s by which case what it matches is — where
 * that is a value a helper or a behavior called by name answers, by the conditions under which that
 * body answers the case.
 *
 * <p>Held against the same conditions written out as an {@code if}, which is read by the rules for
 * comparing numbers and joining truths alone: the two coming to one proposition is what says the arm
 * states what chooses it, nothing added and nothing dropped.
 */
class AnArmARunEntersStatesWhatChoosesItTest {

    private static final String BOUNDED = """
            data Bounded = Int
                invariant low = value >= 1
                invariant high = value <= 10
            """;

    @Test
    void theBuiltArmIsEveryClauseHolding() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms(BOUNDED, "Bounded", """
                {
                    guard Bounded(n) as b else
                        | low  -> 1
                        | high -> 2
                    3
                }""");
        assertEquals(stated("n >= 1 && n <= 10"), arms.get(new MeaningsOfABody.Part.Built()));
    }

    /** Clauses are checked in the order they are declared, so the one a failure names held none of
     *  the ones before it to fail. */
    @Test
    void aDepartureNamingAClauseIsThatClauseFailingFirst() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms(BOUNDED, "Bounded", """
                {
                    guard Bounded(n) as b else
                        | low  -> 1
                        | high -> 2
                    3
                }""");
        assertEquals(stated("n < 1"), arms.get(departed("low")));
        assertEquals(stated("n >= 1 && n > 10"), arms.get(departed("high")));
    }

    @Test
    void aDepartureNamingNoClauseAnswersEveryClauseNoOtherDepartureNames() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms("""
                data Loose = Int
                    invariant value >= 0
                    invariant capped = value <= 100
                """, "Loose", """
                {
                    guard Loose(n) as b else
                        | capped -> 1
                        | _      -> 2
                    3
                }""");
        assertEquals(stated("n < 0"), arms.get(new MeaningsOfABody.Part.Departed(Optional.empty())));
        assertEquals(stated("n >= 0 && n > 100"), arms.get(departed("capped")));
    }

    /** A clause the reading stops in still stands in its place: the departure after it is taken
     *  only where it held, which is not known. */
    @Test
    void aClauseNotReadStandsBeforeTheClausesAfterIt() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms("""
                data Odd = Int
                    invariant odd = Int.floorMod(100, value) == 1
                    invariant high = value <= 10
                """, "Odd", """
                {
                    guard Odd(n) as b else
                        | odd  -> 1
                        | high -> 2
                    3
                }""");
        Proposition.All high = assertInstanceOf(Proposition.All.class, arms.get(departed("high")));
        assertTrue(high.parts().contains(stated("n > 10")), () -> high.toString());
        assertTrue(high.parts().stream().anyMatch(Proposition.Unread.class::isInstance),
                () -> "the clause before it is in it, unread: " + high);
    }

    @Test
    void anArmOfAMatchOnAHelpersAnswerIsWhereTheHelperAnswersItsCase() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms("""
                data Big
                data Small
                data Size = Big | Small

                let kind (n: Int): Size = if n > 5 then Big else Small
                """, null, """
                match kind(n) with
                    | Big   -> 1
                    | Small -> 2""");
        assertEquals(stated("n > 5"), arms.get(new MeaningsOfABody.Part.OfACase(0)));
        assertEquals(stated("n <= 5"), arms.get(new MeaningsOfABody.Part.OfACase(1)));
    }

    /** The behavior's body is read where the call stands, its parameter standing for what the call
     *  handed. */
    @Test
    void anArmOfAMatchOnABehaviorsAnswerIsWhereItsBodyAnswersItsCaseOfWhatTheCallHanded() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms(SIZED, null, """
                match kind(n) with
                    | Big   -> 1
                    | Small -> 2""");
        assertEquals(stated("n > 5"), arms.get(new MeaningsOfABody.Part.OfACase(0)));
        assertEquals(stated("n <= 5"), arms.get(new MeaningsOfABody.Part.OfACase(1)));
    }

    /** A call handing the behavior a value worked out of the input is read the same way: the
     *  body's {@code m > 5} with {@code n + 1} for {@code m}. */
    @Test
    void aBehaviorHandedAValueWorkedOutOfTheInputAnswersItsCaseOfThatValue() {
        Map<MeaningsOfABody.Part.Arm, Proposition> arms = arms(SIZED, null, """
                match kind(n + 1) with
                    | Big   -> 1
                    | Small -> 2""");
        assertEquals(stated("n > 4"), arms.get(new MeaningsOfABody.Part.OfACase(0)));
        assertEquals(stated("n <= 4"), arms.get(new MeaningsOfABody.Part.OfACase(1)));
    }

    private static final String SIZED = """
            data Big
            data Small

            behavior kind : (m: Int) -> Big | Small
            let kind (m) = if m > 5 then Big else Small
            """;

    private static MeaningsOfABody.Part.Departed departed(String clause) {
        return new MeaningsOfABody.Part.Departed(Optional.of(new ClauseName(clause)));
    }

    /** What the condition of {@code f}'s one fork states, its fork written as {@code condition}. */
    private static Proposition stated(String condition) {
        Model model = model("", null, "if %s then 1 else 0".formatted(condition));
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(model.analysis.core()),
                "the body is the fork");
        return Pullback.ofATruth(fork.cond(), model.reads, model.inputs.reading(model.rules),
                Optional.empty()).proposition();
    }

    /** What a run entering each arm of {@code f}'s fork states, as the body's meanings file it. */
    private static Map<MeaningsOfABody.Part.Arm, Proposition> arms(String declarations,
                                                                   String constructs, String body) {
        Model model = model(declarations, constructs, body);
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(model.analysis,
                () -> model.inputs.reading(model.rules), model.reads, model.rules.symbols(),
                model.rules.newtypes());
        Map<MeaningsOfABody.Part.Arm, Proposition> out = new LinkedHashMap<>();
        meanings.stated().forEach((site, meaning) -> {
            if (site.part() instanceof MeaningsOfABody.Part.Arm arm
                    && site.construct().origin().owner()
                    instanceof WrittenOwner.Body(var _, String definition)
                    && definition.equals("f")) {
                out.put(arm, meaning.states());
            }
        });
        return out;
    }

    private record Model(AnalysisBody analysis, InputDomain inputs, RuleReadingSource rules,
                         InputReads reads) {}

    private static Model model(String declarations, String constructs, String body) {
        String source = "module demo\n\n" + declarations + """

                behavior f : (n: Int) -> Int
                %s
                let f (n) =
                %s
                """.formatted(constructs == null ? "" : "    constructs " + constructs,
                body.indent(4));
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles:\n" + source);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return new Model(analysis, inputs, rules, reads);
    }
}
