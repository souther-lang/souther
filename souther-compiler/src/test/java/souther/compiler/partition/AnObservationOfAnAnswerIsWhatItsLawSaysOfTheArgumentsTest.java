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
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.Unsayable;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An observation of what an operation answers states what the operation's law says of the
 * arguments it was handed, each part read where it stands.
 *
 * <p>Held against a spelling an author could have written instead, over the arguments themselves:
 * the two coming to one proposition is what says the law was carried across the call and nothing was
 * added or dropped on the way.
 */
class AnObservationOfAnAnswerIsWhatItsLawSaysOfTheArgumentsTest {

    private static final String INPUT = """
            data Box = { xs: List<Int>, ys: List<Int>, n: Int, s: String, t: String, set: Set<Int> }
            """;

    /** Asked for some and handed some: a disjunction over the arguments, and not a silence. */
    @Test
    void aTakeHoldsSomethingWhereItWasAskedForSomeAndHandedSome() {
        assertEquals(stated("if b.n >= 1 && List.length(b.xs) >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.take(b.n, b.xs))) then 1 else 0"));
    }

    /** A count below nought drops nothing, so what is left is the list where it holds anything. */
    @Test
    void aDropHoldsSomethingWhereTheListHoldsMoreThanItDrops() {
        assertEquals(stated("if List.length(b.xs) >= 1 && List.length(b.xs) - b.n >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.drop(b.n, b.xs))) then 1 else 0"));
    }

    /** Two lists put end to end, written as the operation or as the operator, hold something where
     *  either does. */
    @Test
    void anAppendHoldsSomethingWhereEitherHalfDoesWrittenEitherWay() {
        Proposition either = stated("if List.length(b.xs) >= 1 || List.length(b.ys) >= 1"
                + " then 1 else 0");
        assertEquals(either, stated("if Bool.not(List.isEmpty(List.append(b.xs, b.ys)))"
                + " then 1 else 0"));
        assertEquals(either, stated("if Bool.not(List.isEmpty(b.xs ++ b.ys)) then 1 else 0"));
        assertEquals(stated("if String.length(b.s) >= 1 || String.length(b.t) >= 1 then 1 else 0"),
                stated("if Bool.not(String.isEmpty(b.s ++ b.t)) then 1 else 0"));
    }

    /**
     * A law naming the element of a container the source wrote out is read of each value it
     * writes, as that value: lists put end to end hold something where one of those written does.
     */
    @Test
    void aLawOverValuesWrittenOutIsReadOfEachOfThem() {
        assertEquals(stated("if List.length(b.xs) >= 1 || List.length(b.ys) >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.concat([b.xs, b.ys]))) then 1 else 0"));
        assertEquals(new Proposition.Always(true),
                stated("if Bool.not(List.isEmpty(List.concat([[1], b.xs]))) then 1 else 0"));
        assertEquals(stated("if String.length(b.s) >= 1 then 1 else 0"),
                stated("if Bool.not(String.isEmpty(String.concat([\"\", b.s]))) then 1 else 0"));
    }

    /** How many values written out meet a statement is a number where each of them settles it,
     *  and no linear one of the input where one turns on it. */
    @Test
    void aCountOfValuesWrittenOutIsANumberWhereEachSettlesIt() {
        assertEquals(new Proposition.Always(true), stated(
                "if List.length(List.filter(x -> x > 0, [1, 2, -1])) == 2 then 1 else 0"));
        assertInstanceOf(WhyUnread.OutsideTheLinearFragment.class, Proposition.firstStopIn(
                stated("if List.length(List.filter(x -> x > 0, [b.n, 1])) == 2 then 1 else 0")));
    }

    /** What a set holds once a value is taken out is some other value, read as the quantifier over
     *  the set's element. */
    @Test
    void aSetWithAValueTakenOutHoldsSomeOtherValue() {
        TermPath set = TermPath.of("b").then("set");
        assertEquals(new Proposition.Some(set, new Proposition.SameValue(
                        new DecisionSubject.AnInput(set.element()),
                        new DecisionSubject.AnInput(TermPath.of("b").then("n")), false), true),
                stated("if Bool.not(Set.isEmpty(Set.remove(b.n, b.set))) then 1 else 0"));
    }

    /** A trimmed string being empty comes to every character being whitespace, which no condition
     *  here says: the reading stops on that, and not on a law nobody wrote. */
    @Test
    void aTrimmedStringBeingEmptyStopsOnWhatTheDomainHasNoWordsFor() {
        Proposition stated = stated("if String.isEmpty(String.trim(b.s)) then 1 else 0");
        WhyUnread why = Proposition.firstStopIn(stated);
        WhyUnread.NoWordsFor closed = assertInstanceOf(WhyUnread.NoWordsFor.class, why);
        assertEquals(Unsayable.EVERY_CHARACTER_IS_WHITESPACE, closed.proposition());
    }

    /**
     * How many elements a filter keeps held against nought is whether some element is kept, which
     * the filter's witness law reads the same check as: whichever was written, and whichever rule
     * read it, one proposition.
     */
    @Test
    void aCountHeldAgainstNoughtIsWhetherSomeElementMeetsIt() {
        String count = "List.length(List.filter(x -> x > b.n, b.xs))";
        Proposition some = stated("if Bool.not(List.isEmpty(List.filter(x -> x > b.n, b.xs)))"
                + " then 1 else 0");
        assertInstanceOf(Proposition.Some.class, some);
        for (String atLeastOne : List.of(count + " >= 1", count + " > 0", count + " /= 0",
                "1 <= " + count)) {
            assertEquals(some, stated("if " + atLeastOne + " then 1 else 0"), atLeastOne);
            for (Proposition byARule : byEachRule("if " + atLeastOne + " then 1 else 0")) {
                assertEquals(some, byARule, atLeastOne);
            }
        }
        for (String none : List.of(count + " == 0", count + " < 1", count + " <= 0")) {
            assertEquals(some.denied(), stated("if " + none + " then 1 else 0"), none);
        }
        assertEquals(new Proposition.Always(true), stated("if " + count + " >= 0 then 1 else 0"));
        assertEquals(new Proposition.Always(false), stated("if " + count + " < 0 then 1 else 0"));
    }

    /** Held against any other number, a count says how many, and is kept as the relation. */
    @Test
    void aCountHeldAgainstAnotherNumberSaysHowMany() {
        Proposition exactlyOne = stated(
                "if List.length(List.filter(x -> x > b.n, b.xs)) == 1 then 1 else 0");
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, exactlyOne);
        Relation.Affine relation = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertTrue(relation.form().coefs().keySet().stream()
                        .anyMatch(quantity -> quantity instanceof Quantity.HowManyMeet),
                "the relation is over the count: " + exactlyOne);
        assertNull(Proposition.firstStopIn(stated(
                "if List.length(List.filter(x -> x > 3, b.xs)) >= 2 then 1 else 0")));
    }

    /** What a count is about is the element where it stands, so the name an author gave the
     *  element does not make it another count. */
    @Test
    void aCountIsTheSameWhateverItsElementIsCalled() {
        assertEquals(stated("if List.length(List.filter(x -> x > b.n, b.xs)) == 2 then 1 else 0"),
                stated("if List.length(List.filter(y -> y > b.n, b.xs)) == 2 then 1 else 0"));
        assertNotEquals(stated("if List.length(List.filter(x -> x > b.n, b.xs)) == 2 then 1 else 0"),
                stated("if List.length(List.filter(x -> x > b.n, b.ys)) == 2 then 1 else 0"));
    }

    /** A count of a container inside a statement about some element of that same container would
     *  name two elements one subject, and is not read. */
    @Test
    void aCountInsideAQuantifierOverItsOwnContainerIsNotRead() {
        Proposition nested = stated("if List.any(x -> List.length(List.filter(y -> y > x, b.xs))"
                + " == 1, b.xs) then 1 else 0");
        assertInstanceOf(WhyUnread.TwoElementsOfOneContainer.class,
                Proposition.firstStopIn(nested), nested.toString());
    }

    /** How many what a mapping answers holds is how many it was handed, read as that one's size. */
    @Test
    void aSizeOfAMappingIsTheSizeOfWhatItWasHanded() {
        assertEquals(stated("if List.length(b.xs) == 2 then 1 else 0"),
                stated("if List.length(List.map(x -> x + 1, b.xs)) == 2 then 1 else 0"));
        assertEquals(stated("if List.length(b.xs) + List.length(b.ys) == 2 then 1 else 0"),
                stated("if List.length(b.xs ++ b.ys) == 2 then 1 else 0"));
    }

    /** What the condition of the one fork of a body written {@code body} states. */
    private static Proposition stated(String body) {
        Fork fork = fork(body);
        return Pullback.ofATruth(fork.condition(), fork.reads(), fork.read(), Optional.empty())
                .proposition();
    }

    /** What each rule that reads all of the condition of the one fork of {@code body}, a
     *  comparison, concludes. */
    private static List<Proposition> byEachRule(String body) {
        Fork fork = fork(body);
        StatedComparison comparison = BooleanMeaning.asAComparison(fork.condition())
                .orElseThrow(() -> new AssertionError(body + " is a comparison"));
        return Pullback.byEachRule(comparison, fork.reads(), fork.read()).stream()
                .filter(each -> !Proposition.leavesSomethingUnread(each)).toList();
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
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return new Fork(fork.cond(), reads, inputs.reading(rules));
    }
}
