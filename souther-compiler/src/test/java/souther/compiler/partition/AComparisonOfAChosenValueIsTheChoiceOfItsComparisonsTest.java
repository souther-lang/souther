package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison of a value chosen by cases states, in each case, the comparison of what that case
 * answers — the same proposition as the choice of those comparisons written out.
 *
 * <p>Held against the spelling an author could have written instead, since that one is read by the
 * rules for a choice of truths and for a comparison of numbers alone: the two coming to one
 * proposition is what says the choice was carried out of the comparison and nothing was added or
 * dropped on the way. The cases are the language's and the library's alike.
 */
class AComparisonOfAChosenValueIsTheChoiceOfItsComparisonsTest {

    private static final String INPUT = """
            data Kind = Small | Large
            data Box = { x: Int, y: Int, open: Bool, kind: Kind }
            """;

    @Test
    void anIfOnEitherSideIsItsArmsCompared() {
        Proposition writtenOut = stated(
                "if (if b.open then b.x >= 1800 else b.x >= 1300) then 1 else 0");
        assertEquals(writtenOut,
                stated("if b.x >= (if b.open then 1800 else 1300) then 1 else 0"));
        assertEquals(writtenOut,
                stated("if (if b.open then 1800 else 1300) <= b.x then 1 else 0"));
        assertFalse(unreadIn(writtenOut), "every part of it is read");
    }

    /**
     * A name given the choice before the other side was bound: each side is related where it was
     * read, so what the case answers and the value it is compared with are both found.
     */
    @Test
    void aChoiceGivenANameIsComparedWithASideBoundAfterIt() {
        assertEquals(stated("if (if b.open then b.x >= 1800 else b.x >= 1300) then 1 else 0"),
                stated("""
                        {
                            let ceiling = if b.open then 1800 else 1300
                            let v = b.x
                            if v >= ceiling then 1 else 0
                        }"""));
    }

    @Test
    void bothSidesChosenAreEveryPairOfTheirCases() {
        Proposition stated = stated(
                "if (if b.open then b.x else b.y) > (if b.kind == Small then 1 else 2) then 1 else 0");
        assertFalse(unreadIn(stated), "every case of each side is read: " + stated);
    }

    @Test
    void aMatchIsItsArmsCompared() {
        assertEquals(stated("""
                        if (match b.kind with
                                | Small -> b.x > 1
                                | Large -> b.x > 2) then 1 else 0"""),
                stated("""
                        if b.x > (match b.kind with
                                      | Small -> 1
                                      | Large -> 2) then 1 else 0"""));
    }

    /**
     * An operation the library defines by how its arguments stand is chosen by those cases, and what
     * a case answers is one of its arguments.
     */
    @Test
    void anOperationDefinedByCasesIsItsCasesCompared() {
        Proposition least = stated("if Int.min(b.x, b.y) < 10 then 1 else 0");
        assertEquals(stated("if (if b.x < b.y then b.x < 10 else b.y < 10) then 1 else 0"), least);
        assertInstanceOf(Derivation.AComparisonOfAChoice.class,
                derived("if Int.min(b.x, b.y) < 10 then 1 else 0"),
                "read as the cases of the operation, and not as a number nothing reads");
        assertFalse(unreadIn(least));
    }

    /**
     * A truth held against one written out, read as the comparison it is written as, is that truth
     * whatever chooses it: a truth chosen by cases is read as the choice it is, and not split into
     * comparisons of truths as numbers. Read as a condition, the same spelling is a truth under a
     * denial or none, and the two readings state one thing.
     */
    @Test
    void aTruthChosenByCasesHeldAgainstAWrittenTruthIsThatTruth() {
        String chosen = "(if b.open then b.x > 1 else b.y > 2)";
        Proposition itself = stated("if " + chosen + " then 1 else 0");
        assertFalse(unreadIn(itself));
        for (String spelled : List.of(chosen + " == true", "false /= " + chosen)) {
            assertEquals(itself, compared("if " + spelled + " then 1 else 0"), spelled);
            assertEquals(itself, stated("if " + spelled + " then 1 else 0"), spelled);
        }
        assertEquals(itself.denied(), compared("if " + chosen + " == false then 1 else 0"));
    }

    /** What the condition of the one fork of {@code body}, written as a comparison, states read as
     *  that comparison rather than as a truth. */
    private static Proposition compared(String body) {
        Fork fork = fork(body);
        StatedComparison comparison = BooleanMeaning.asAComparison(fork.condition())
                .orElseThrow(() -> new AssertionError(body + " is a comparison"));
        return Pullback.ofAComparison(comparison, fork.reads(), fork.read(), Optional.empty())
                .proposition();
    }

    /** No comparison of a value nothing chooses is taken by this rule. */
    @Test
    void aComparisonOfNoChoiceIsNotOne() {
        assertFalse(derived("if b.x >= b.y then 1 else 0")
                        instanceof Derivation.AComparisonOfAChoice,
                "a comparison of two numbers is read as one");
    }

    private static boolean unreadIn(Proposition stated) {
        return switch (stated) {
            case Proposition.Unread _ -> true;
            case Proposition.All all -> all.parts().stream()
                    .anyMatch(AComparisonOfAChosenValueIsTheChoiceOfItsComparisonsTest::unreadIn);
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(AComparisonOfAChosenValueIsTheChoiceOfItsComparisonsTest::unreadIn);
            case Proposition.Some some -> unreadIn(some.ofTheElement());
            default -> false;
        };
    }

    /** What the condition of the one fork of a body written {@code body} states. */
    private static Proposition stated(String body) {
        return pulled(body).proposition();
    }

    /** How the condition of the one fork of a body written {@code body} was read. */
    private static Derivation derived(String body) {
        return pulled(body).meaning().how();
    }

    private static Pullback.Pulled pulled(String body) {
        Fork fork = fork(body);
        return Pullback.ofATruth(fork.condition(), fork.reads(), fork.read(), Optional.empty());
    }

    private record Fork(Core condition, InputReads reads, InputReading read) {}

    /** The condition of the one fork of a body written {@code body}, as the reading meets it. */
    private static Fork fork(String body) {
        String model = "module demo\n\n" + INPUT + """

                behavior f : (b: Box) -> Int
                let f (b) =
                    %s
                """.formatted(body.indent(4).strip());
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + body);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return new Fork(fork.cond(), reads, inputs.reading(rules));
    }
}
