package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value held against what an operation of the library answers of another value of the input is
 * read as a relation of the two positions, and what it leaves each of them is what the other side
 * is shown to reach.
 *
 * <p>{@code d == String.lowercase(s)} is read to the end however the answer reaches the comparison
 * — written there, under a name, or handed to a helper. It leaves {@code s} undivided: whatever
 * {@code s} holds, some {@code d} meets the answer and some does not. It is not shown to leave
 * {@code d} so: no lowercased string holds a capital, so a {@code d} holding one settles the
 * comparison whatever {@code s} is, and nothing here works out which strings the operation
 * answers.
 *
 * <p>What the answer is is the operation and what it was handed, and not where it was made from:
 * {@code String.lowercase(s)} and {@code String.uppercase(s)} are made of one position and are two
 * values. A statement holding two values made of one position against each other, or one against
 * a constant, says which values that position holds, and is not read here.
 */
class AValueHeldAgainstWhatAnOperationAnswersRelatesTheTwoTest {

    private static String measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> said(String report) {
        return report.lines().map(String::strip).filter(line -> line.startsWith("· not read")
                || line.startsWith("· no line")).toList();
    }

    private static String relates(String at, String position) {
        return "· no line: comparison@" + at + " — it relates the value here to another value rather"
                + " than dividing the values here, about `" + position + "`";
    }

    private static String notShown(String at, String position) {
        return "· not read: comparison@" + at + " — what it states was read, and it relates the"
                + " value here to another value not shown to reach every value here, so which values"
                + " here settle it on their own is not worked out, about `" + position + "`";
    }

    private static String madeFrom(String at, String position) {
        return "· not read: comparison@" + at + " — it is about a value made from this one, and"
                + " what it says about the values here is not worked out, about `" + position + "`";
    }

    @Test
    void aDomainHeldAgainstALowercasedAddressHandedToAHelperIsReadAsARelationOfTheTwo() {
        String report = measured("""
                module w1
                data Account = { id: Int, domain: String? }
                let hasDomain (d: String, a: Account): Bool =
                    match a.domain with
                        | Some own -> own == d
                        | None     -> false
                behavior m : (s: String, a: Account) -> Bool
                let m (s, a) = hasDomain(String.lowercase(s), a)
                """);
        // Each at the call that handed the helper its values, which is where the comparison inside
        // it was read.
        assertEquals(Set.of(notShown("5:27", "a.domain@Some") + " in hasDomain@8:16",
                        relates("5:27", "s") + " in hasDomain@8:16"),
                Set.copyOf(said(report)), report);
    }

    @Test
    void theAnswerWrittenThereOrUnderANameIsTheSameRelation() {
        assertEquals(Set.of(notShown("3:18", "d"), relates("3:18", "s")), Set.copyOf(said(measured("""
                module w1
                behavior m : (s: String, d: String) -> Bool
                let m (s, d) = d == String.lowercase(s)
                """))));
        assertEquals(Set.of(notShown("4:4", "d"), relates("4:4", "s")), Set.copyOf(said(measured("""
                module w1
                behavior m : (s: String, d: String) -> Bool
                let m (s, d) = { let l = String.lowercase(s)
                 d == l }
                """))));
    }

    /** Two values being one or not is a relation of the two positions as two values being one
     *  is. */
    @Test
    void aDenialLeavesTheSameTwo() {
        assertEquals(Set.of(notShown("3:18", "d"), relates("3:18", "s")),
                Set.copyOf(said(measured("""
                        module w1
                        behavior m : (s: String, d: String) -> Bool
                        let m (s, d) = d /= String.lowercase(s)
                        """))));
    }

    /**
     * Held in order, the answer may stand at the least string, which every string of spaces is
     * trimmed to and no {@code d} is below: each of them settles the comparison whatever {@code d}
     * holds, so the order is not shown to leave {@code s} undivided.
     */
    @Test
    void anOrderAgainstAnAnswerAtTheEndOfItsTypeIsNotShownToLeaveItsPlaceUndivided() {
        assertEquals(Set.of(notShown("3:18", "d"), notShown("3:18", "s")),
                Set.copyOf(said(measured("""
                        module w1
                        behavior m : (s: String, d: String) -> Bool
                        let m (s, d) = d < String.trim(String.lowercase(s))
                        """))));
    }

    /** Two answers of positions apart, neither of which is shown to reach every value of the
     *  other: a lowercased string is never an uppercased one with a letter in it. */
    @Test
    void twoAnswersOfPositionsApartAreNotShownToLeaveEitherUndivided() {
        assertEquals(Set.of(notShown("3:36", "s"), notShown("3:36", "t")),
                Set.copyOf(said(measured("""
                        module w1
                        behavior m : (s: String, t: String) -> Bool
                        let m (s, t) = String.lowercase(t) == String.uppercase(s)
                        """))));
    }

    @Test
    void anAnswerThatCountsToANumberIsReadWhereItIsOneValueAndNotWhereItIsHeldInOrder() {
        assertEquals(Set.of(relates("3:18", "d"), relates("3:18", "DateTime.toDate(t)")),
                Set.copyOf(said(measured("""
                        module w1
                        behavior m : (d: Date, t: DateTime) -> Bool
                        let m (d, t) = d == DateTime.toDate(t)
                        """))));
        assertEquals(Set.of(relates("3:18", "d"), relates("3:18", "DateTime.toDate(t)")),
                Set.copyOf(said(measured("""
                        module w1
                        behavior m : (d: Date, t: DateTime) -> Bool
                        let m (d, t) = d < DateTime.toDate(t)
                        """))));
    }

    @Test
    void twoAnswersOfOnePositionOrOneAgainstAConstantAreNotARelation() {
        assertEquals(List.of(madeFrom("3:33", "s") + ", at 3:13"), said(measured("""
                module w1
                behavior m : (s: String) -> Bool
                let m (s) = String.lowercase(s) == String.uppercase(s)
                """)));
        assertEquals(List.of(madeFrom("3:33", "s") + ", at 3:13"), said(measured("""
                module w1
                behavior m : (s: String) -> Bool
                let m (s) = String.lowercase(s) == "abc"
                """)));
        String againstItself = measured("""
                module w1
                data P = { s: String, n: Int }
                behavior m : (p: P) -> Bool
                let m (p) = p.s == String.lowercase(p.s)
                """);
        assertTrue(said(againstItself).stream().allMatch(line -> line.contains("not read")),
                againstItself);
    }

    @Test
    void answersOfTwoElementsOfOneContainerAreNotReadAsTheElementsThemselvesAreNot() {
        for (String compared : List.of("x.a == y.b",
                "String.lowercase(x.a) == String.uppercase(y.b)",
                "{ let l = String.lowercase(y.b)\n x.a == l }")) {
            String report = measured("""
                    module w1
                    data E = { a: String, b: String }
                    behavior m : (xs: List<E>) -> Bool
                    let m (xs) = List.any(x -> List.any(y -> %s, xs), xs)
                    """.formatted(compared));
            List<String> said = said(report);
            assertEquals(2, said.size(), report);
            assertTrue(said.stream().allMatch(line -> line.startsWith("· not read")), report);
        }
    }

    @Test
    void aRowThroughTheRelationIsTheRunsToDecideForWhatTheOperationAnswers() {
        String report = measured("""
                module w1
                behavior m : (s: String, d: String) -> Int
                let m (s, d) = if d == String.lowercase(s) then 1 else 0
                example m
                    | ("A", "a") -> 1
                """);
        assertTrue(report.contains("a condition the run decides, since nothing here composes a row"
                + " for what an operation answers of the input, which no position holds"), report);
    }

    @Test
    void oneAnswerOnBothSidesCutsNothing() {
        assertEquals(List.of("· no line: comparison@3:33 — it was read to the end and cuts nothing"
                + " this position appears in, about `s`"), said(measured("""
                module w1
                behavior m : (s: String) -> Bool
                let m (s) = String.lowercase(s) == String.lowercase(s)
                """)));
    }

    @Test
    void theAnswerIsTheOperationAndWhatItWasHanded() {
        Proposition lower = stated("b.t == String.lowercase(b.s)");
        assertInstanceOf(Proposition.Compared.class, lower);
        assertEquals(lower, stated("{ let l = String.lowercase(b.s)\n l == b.t }"));
        assertNotEquals(lower, stated("b.t == String.uppercase(b.s)"));
        assertNotEquals(lower, stated("b.t == b.s"));
        assertNotEquals(lower, stated("b.t == String.lowercase(b.u)"));
    }

    private static Proposition stated(String condition) {
        String model = """
                module demo
                data Box = { s: String, t: String, u: String }
                behavior f : (b: Box) -> Int
                let f (b) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()),
                "the body is the fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
