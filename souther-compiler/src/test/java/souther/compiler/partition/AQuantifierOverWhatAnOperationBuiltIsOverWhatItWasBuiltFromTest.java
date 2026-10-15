package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What some element, or how many elements, of a container an operation built meet is what the
 * operation says of the container it was built from: another order of the same elements has the
 * same, what was kept of them has those meeting what it kept by as well, and a set made of the
 * values of a list or of what a closure answered holds some element meeting a statement where the
 * source does.
 *
 * <p>Held against the same question asked of the source the way an author could have written it,
 * and against the questions that were not asked: how many of a set meet a statement is not how many
 * of what it was made of do, since a set holds a value once however many elements gave it.
 */
class AQuantifierOverWhatAnOperationBuiltIsOverWhatItWasBuiltFromTest {

    @Test
    void anotherOrderOfTheElementsHasTheSameSomeAndTheSameCount() {
        for (String order : List.of("List.reverse(xs)", "List.sort(xs)",
                "List.reverse(List.sort(xs))")) {
            assertEquals(stated("List.length(List.filter(x -> x > 0, xs)) >= 1"),
                    stated("List.length(List.filter(x -> x > 0, " + order + ")) >= 1"), order);
            assertEquals(stated("List.length(List.filter(x -> x > 0, xs)) >= 2"),
                    stated("List.length(List.filter(x -> x > 0, " + order + ")) >= 2"), order);
        }
    }

    /** What some element of a filter's answer meets is met by an element that was kept too. */
    @Test
    void whatWasKeptIsKeptByTheClosureItWasKeptBy() {
        assertEquals(stated("List.length(List.filter(x -> x > 0 && x < 9, xs)) >= 1"),
                stated("List.length(List.filter(x -> x > 0, List.filter(x -> x < 9, xs))) >= 1"));
        assertNotEquals(stated("List.length(List.filter(x -> x > 0, xs)) >= 1"),
                stated("List.length(List.filter(x -> x > 0, List.filter(x -> x < 9, xs))) >= 1"),
                "an element meeting only the closure it is asked about is not one that was kept");
        assertEquals(stated("List.length(List.filter(x -> x > 0 && x < 9 && x /= 5, xs)) >= 1"),
                stated("List.length(List.filter(x -> x > 0, List.filter(x -> x < 9,"
                        + " List.filter(x -> x /= 5, xs)))) >= 1"));
        assertEquals(stated("Set.size(Set.filter(x -> x > 0 && x < 9, ys)) >= 1"),
                stated("Set.size(Set.filter(x -> x > 0, Set.filter(x -> x < 9, ys))) >= 1"));
    }

    @Test
    void howManyWereKeptIsHowManyMeetWhatTheyWereKeptByAndWhatIsAsked() {
        assertEquals(stated("List.length(List.filter(x -> x > 0 && x < 9, xs)) >= 2"),
                stated("List.length(List.filter(x -> x > 0, List.filter(x -> x < 9, xs))) >= 2"));
        assertEquals(stated("Set.size(Set.filter(x -> x > 0 && x < 9, ys)) >= 2"),
                stated("Set.size(Set.filter(x -> x > 0, Set.filter(x -> x < 9, ys))) >= 2"));
    }

    /** A mapping between the two, or a reordering, does not change what was kept. */
    @Test
    void aMappingAndAFilterComposeLevelByLevel() {
        assertEquals(stated("List.length(List.filter(x -> x + 1 > 0 && x < 9, xs)) >= 1"),
                stated("List.length(List.filter(y -> y > 0, List.map(x -> x + 1,"
                        + " List.filter(x -> x < 9, xs)))) >= 1"));
        assertEquals(stated("List.length(List.filter(x -> x > 0 && x < 9, xs)) >= 2"),
                stated("List.length(List.filter(x -> x > 0, List.reverse("
                        + "List.filter(x -> x < 9, List.sort(xs))))) >= 2"));
    }

    @Test
    void aSetMadeOfAListHoldsAnElementMeetingAStatementWhereTheListDoes() {
        assertEquals(stated("List.length(List.filter(x -> x > 0, xs)) >= 1"),
                stated("Set.size(Set.filter(x -> x > 0, Set.fromList(xs))) >= 1"));
        assertEquals(stated("List.length(List.filter(x -> x > 0 && x < 9, xs)) >= 1"),
                stated("Set.size(Set.filter(x -> x > 0, Set.filter(x -> x < 9,"
                        + " Set.fromList(xs)))) >= 1"));
    }

    @Test
    void aSetMappedHoldsAnElementMeetingAStatementWhereTheAnswerOnSomeElementDoes() {
        assertEquals(stated("Set.size(Set.filter(x -> x + 1 > 0, ys)) >= 1"),
                stated("Set.size(Set.filter(y -> y > 0, Set.map(x -> x + 1, ys))) >= 1"));
        assertEquals(stated("Set.size(Set.filter(x -> x + 1 > 0 && x < 9, ys)) >= 1"),
                stated("Set.size(Set.filter(y -> y > 0, Set.map(x -> x + 1,"
                        + " Set.filter(x -> x < 9, ys)))) >= 1"));
    }

    /**
     * Some piece of a string split at one code point holding something once trimmed is the string
     * holding a code point that is neither whitespace nor that one — in whichever way the pieces
     * are filtered, mapped and made a set of on the way to being asked.
     */
    @Test
    void somePieceOfASplitHoldingSomethingIsTheStringHoldingACodePointBesideTheSeparator() {
        String trimmed = "String.length(String.trim(p)) >= 1";
        Proposition direct = stated("List.length(List.filter(p -> " + trimmed
                + ", String.split(\",\", t))) >= 1");
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, direct);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertEquals(List.of("#(not whitespace nor U+2C)(t)"), affine.form().coefs().keySet()
                .stream().map(Object::toString).toList(), "the one number it is about");
        assertEquals(direct, stated("List.length(List.filter(p -> " + trimmed
                + ", List.reverse(String.split(\",\", t)))) >= 1"));
        assertEquals(direct, stated("List.length(List.filter(p -> " + trimmed
                + ", List.filter(p -> " + trimmed + ", String.split(\",\", t)))) >= 1"));
        assertEquals(direct, stated("Set.size(Set.filter(p -> String.length(p) >= 1,"
                + " Set.map(p -> String.lowercase(String.trim(p)),"
                + " Set.fromList(String.split(\",\", t))))) >= 1"));
        assertEquals(direct.denied(), stated("Set.size(Set.filter(p -> String.length(p) >= 1,"
                + " Set.map(p -> String.lowercase(String.trim(p)),"
                + " Set.fromList(String.split(\",\", t))))) == 0"));
    }

    /**
     * What is said of pieces besides that one of them holds something is not what the string
     * holds, and is not read: how many hold something, that one is blank, a separator longer than
     * a code point or one the model does not write out all depend on how the separator stands in
     * the string.
     */
    @Test
    void whatElseIsAskedOfThePiecesOfASplitIsNotReadAsWhatTheStringHolds() {
        for (String asked : List.of(
                "List.length(List.filter(p -> String.length(String.trim(p)) >= 1,"
                        + " String.split(\",\", t))) >= 2",
                "List.length(List.filter(p -> String.length(String.trim(p)) == 0,"
                        + " String.split(\",\", t))) >= 1",
                "List.length(List.filter(p -> String.length(p) >= 3, String.split(\",\", t))) >= 1",
                "List.length(List.filter(p -> String.length(String.trim(p)) >= 1,"
                        + " List.filter(p -> String.length(p) >= 0, String.split(\",\", t))))"
                        + " >= 1",
                "List.length(List.filter(p -> String.length(String.trim(p)) >= 1,"
                        + " String.split(\"ab\", t))) >= 1",
                "List.length(List.filter(p -> String.length(String.trim(p)) >= 1,"
                        + " String.split(sep, t))) >= 1")) {
            Proposition stated = stated(asked);
            assertTrue(unreadIn(stated), () -> asked + " was read: " + stated);
        }
    }

    /**
     * Two elements of a set may answer one value, and two of a list may be one value, so a count of
     * what meets a statement is a count of the values and no count of the source's elements.
     */
    @Test
    void howManyOfASetMeetAStatementIsNotHowManyOfWhatItWasMadeOfDo() {
        for (String counted : List.of(
                "Set.size(Set.filter(x -> x == 0, Set.map(x -> 0, ys))) >= 2",
                "Set.size(Set.filter(x -> x > 0, Set.map(x -> x + 1, ys))) >= 2",
                "Set.size(Set.filter(x -> x > 0, Set.fromList(xs))) >= 2")) {
            Proposition stated = stated(counted);
            assertTrue(unreadIn(stated), () -> counted + " was read: " + stated);
        }
    }

    private static boolean unreadIn(Proposition stated) {
        return switch (stated) {
            case Proposition.Unread _ -> true;
            case Proposition.All all -> all.parts().stream()
                    .anyMatch(AQuantifierOverWhatAnOperationBuiltIsOverWhatItWasBuiltFromTest::unreadIn);
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(AQuantifierOverWhatAnOperationBuiltIsOverWhatItWasBuiltFromTest::unreadIn);
            case Proposition.Some some -> unreadIn(some.ofTheElement());
            default -> false;
        };
    }

    /** What the condition of {@code f}'s one fork states, its fork written as {@code condition}. */
    private static Proposition stated(String condition) {
        Model model = model(condition);
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(model.analysis.core()),
                "the body is the fork");
        return Pullback.ofATruth(fork.cond(), model.reads, model.inputs.reading(model.rules),
                Optional.empty()).proposition();
    }

    private record Model(AnalysisBody analysis, InputDomain inputs, RuleReadingSource rules,
                         InputReads reads) {}

    private static Model model(String condition) {
        String source = """
                module demo

                behavior f : (xs: List<Int>, ys: Set<Int>, t: String, sep: String) -> Int
                let f (xs, ys, t, sep) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
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
