package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a row is owed for is the line the author wrote, and neither the rule it came from nor the
 * position it was read at.
 *
 * <p>Three identities where there used to be one. Which rule drew the line is provenance and the
 * same value however many lines the rule drew; which line is owed a row is the debt; where that line
 * was read is an occurrence, one per position of every behavior carrying the type. A measure keyed
 * on the occurrence asks for one rule's row once per position — 126 times over {@code crm}'s
 * {@code UserId} — and a measure keyed on the rule asks for one row where the author drew two lines.
 *
 * <p>Written before the debt exists, because the whole of what this change is worth is the answer to
 * "why are these the same debt". Left to be read off whatever the implementation keyed on, that
 * answer lives outside the types and the next reading takes it back.
 */
class ABorderDebtIsTheLineTheAuthorWroteTest {

    /**
     * One clause placing two ends is two debts, and a row at one is not a row at the other.
     *
     * <p>The case a debt keyed on the rule gets wrong. {@code within} is one clause and one
     * {@link souther.compiler.check.RuleRef.Invariant}, and the lines it draws at 1 and at 10 have
     * nothing to say about each other: a row standing at the bottom of the range is no evidence
     * about the top. So the rule is the same value at both and the debt is not.
     */
    @Test
    void aClausesTwoEndsAreTwoDebts() {
        Map<String, BorderAssessment> lines = bordersOf(RANGE, "example.range");
        BorderAssessment bottom = at(lines, "n = 1");
        BorderAssessment top = at(lines, "n = 10");

        assertEquals(bottom.border().obligation().provenance(),
                top.border().obligation().provenance(),
                "one clause drew both, which is what provenance answers");
        assertNotEquals(bottom.border().obligation(), top.border().obligation(),
                "and a row at the bottom of the range is no evidence about the top");
    }

    /**
     * One invariant read at two behaviors is one debt.
     *
     * <p>What issue #1062 is. {@code UserId} says a user id is a string of one character or more,
     * and whether a row standing at length 1 is believed is a question about {@code UserId} — the
     * answer cannot differ between {@code schedule} and {@code touch}, since neither says anything
     * about the length of a user id. Two occurrences and one debt.
     */
    @Test
    void oneInvariantReadAtTwoBehaviorsIsOneDebt() {
        Map<String, BorderAssessment> lines = bordersOf(TWO_BEHAVIORS, "example.two");
        BorderAssessment scheduled = at(lines, "String.length(d.owner) = 1");
        BorderAssessment touched = at(lines, "String.length(t.owner) = 1");

        assertNotEquals(scheduled.border().cut(), touched.border().cut(),
                "the two are read at different positions, which is what an occurrence is");
        assertEquals(scheduled.border().obligation(), touched.border().obligation(),
                "and both are the one line UserId's clause drew");
    }

    /**
     * Two positions of one type in one behavior are one debt too.
     *
     * <p>The same equivalence with the behavior held still, so that nothing can satisfy the one
     * above by keying on the behavior. A row standing at the boundary through {@code owner} is
     * evidence about {@code UserId}, and {@code reviewer} is the same type saying the same thing.
     */
    @Test
    void twoPositionsOfOneTypeInOneBehaviorAreOneDebt() {
        Map<String, BorderAssessment> lines = bordersOf(TWO_POSITIONS, "example.both");

        assertEquals(1,
                lines.values().stream().map(each -> each.border().obligation()).distinct().count(),
                "one clause, one line, one debt — however many positions carry the type: "
                        + lines.keySet());
        assertEquals(2, lines.size(), "read at both of them: " + lines.keySet());
    }

    /**
     * Two clauses cutting at one value are two debts.
     *
     * <p>The other way a debt keyed too widely goes wrong, and the reason a level alone is not the
     * key either. {@code Window} and {@code Slot} each stop a {@code Minute} at 1000, on one carrier
     * and at one value; they are two rules an author wrote and either could be changed without the
     * other. A row at the line one drew establishes nothing about the line the other drew.
     *
     * <p>Beside {@code Minute}'s own lower end, which both records carry and which is one debt. The
     * pair is the measurement: an implementation that told the two 1000s apart by the position they
     * were read at would pass the first half and split the second.
     */
    @Test
    void twoClausesCuttingAtOneValueAreTwoDebts() {
        Map<String, BorderAssessment> lines = bordersOf(TWO_RECORDS, "example.narrow");

        assertNotEquals(at(lines, "x.stop = 1000").border().obligation(),
                at(lines, "y.at = 1000").border().obligation(),
                "two rules drew a line at one value, and each is owed its own row");
        assertEquals(at(lines, "x.stop = 0").border().obligation(),
                at(lines, "y.at = 0").border().obligation(),
                "and one rule drew the lower end of both, which is one row to write");
    }

    /**
     * One clause bounding two numbers of one declaration is two debts.
     *
     * <p>The case a debt keyed on the clause and the value gets wrong, and the reason the number the
     * clause was written about is part of what a debt is. {@code both} places an end at 1 on
     * {@code String.length(name)} and an end at 1 on {@code String.length(code)}: one clause, one
     * carrier, one value, one polarity, and two lines. A row whose {@code name} is one character
     * long says nothing about {@code code}.
     *
     * <p>What the two share is everything an identity read off the rule and the cut would have had
     * to tell them apart by, which is why this is measured rather than argued: the language builds
     * it, so a reading that folds them is a reading that reports one of them covered by the other's
     * row.
     */
    @Test
    void oneClauseBoundingTwoNumbersOfOneDeclarationIsTwoDebts() {
        Map<String, BorderAssessment> lines = bordersOf(TWO_NUMBERS, "example.numbers");
        BorderAssessment name = at(lines, "String.length(p.name) = 1");
        BorderAssessment code = at(lines, "String.length(p.code) = 1");

        assertEquals(name.border().obligation().provenance(),
                code.border().obligation().provenance(), "one clause placed both ends");
        assertEquals(name.border().cut().at(), code.border().cut().at(),
                "at one value of one carrier, so neither the rule nor the level tells them apart");
        assertNotEquals(name.border().obligation(), code.border().obligation(),
                "and the number the clause was written about does");
    }

    /** One clause bounding two numbers of the declaration it is written on. */
    private static final String TWO_NUMBERS = """
            module example.numbers

            data Pair = { name: String, code: String }
                invariant both = String.length(name) >= 1 && String.length(code) >= 1

            data Ok

            behavior f : (p: Pair) -> Ok
            let f (p) = Ok

            example f
                | "a" : (Pair { name = "x", code = "y" }) -> Ok
            """;

    /**
     * One conjunct read through two frames is one debt.
     *
     * <p>The direction the case above does not fix. A clause of {@code Day} is read twice — once
     * from {@code Day}, where it is about {@code value}, and once from the {@code Span} holding it,
     * where it is about {@code d} — and the two readings are merged into one range
     * ({@code DeclaredBounds.and}). What the author wrote is one line either way, so the two are one
     * debt and each position carries two ends rather than four.
     *
     * <p>A second bounded field beside it, because the merge is what this is about: with one field
     * the reading through the record contributes nothing and the model goes past the case without
     * touching it.
     *
     * <p>Measured as the count of borders rather than by comparing two of them, because the way this
     * goes wrong is a border appearing twice: an identity read off the number the clause was written
     * about spells it {@code value} in one reading and {@code d} in the other, and both survive into
     * the cut. Counting is what notices that; asking two borders whether they agree finds one of the
     * pair and never the pair.
     */
    @Test
    void oneConjunctReadThroughTwoFramesIsOneDebt() {
        List<Border> lines = bordersOfThePosition(TWO_FRAMES, "classify", "s.d");

        assertEquals(2, lines.size(),
                () -> "the clause states two ends, so the position has two borders: "
                        + lines.stream().map(Border::label).toList());
        assertEquals(2, lines.stream().map(Border::obligation).distinct().count(),
                "and neither of them is two debts");
    }

    /**
     * Every border of one position, as the partition makes them.
     *
     * <p>Below the report, because that is where a line read twice shows as two. What reaches a
     * report is the assessment, and a border read through two frames arrives there as one entry
     * whichever answer this gives — so a test asking the report would have said the identity was
     * right whatever it was.
     */
    private static List<Border> bordersOfThePosition(String model, String behavior, String path) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        souther.compiler.check.Prepared prepared =
                compilation.db().ask(new souther.compiler.query.Shapes.Prepared(module)).value();
        souther.compiler.check.Symbols symbols =
                souther.compiler.query.Scopes.derived(compilation.db(), module).value();
        Map<String, souther.compiler.check.Sig> sigs = compilation.db()
                .ask(new souther.compiler.query.Bodies.Signatures(module)).value();
        souther.compiler.ast.Hir.SpecBehavior spec =
                (souther.compiler.ast.Hir.SpecBehavior) prepared.behaviors().stream()
                        .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        assertNotNull(sigs.get(behavior), "the model under test compiles");
        souther.compiler.inputs.InputDomain domain =
                souther.compiler.inputs.InputDomain.of(spec, sigs.get(behavior), symbols,
                        souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Partitions.Partitioning partitioning = Partitions.of(spec.name(), domain, symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Axis axis = partitioning.axes().stream()
                .filter(a -> a.path().toString().equals(path)).findFirst().orElseThrow();
        return Partitions.bordersOf(axis, symbols,
                domain.quantities(symbols).runsBetween(axis.term()), new LinesRead());
    }

    /** A newtype's own clause, reached through the record that holds it. */
    private static final String TWO_FRAMES = """
            module example.frames

            data Slot = Int
                invariant value >= 0 && value <= 10

            data Day = Date
                invariant value >= Date("2020-01-01") && value <= Date("2020-01-02")

            data Span = { a: Slot, d: Day }

            data Ok

            behavior classify : (s: Span) -> Ok
            let classify (s) = Ok

            example classify
                | "a" : (Span { a = Slot(1), d = Day(Date("2020-01-01")) }) -> Ok
            """;

    /** One clause placing both ends of a range. */
    private static final String RANGE = """
            module example.range

            data N = Int
                invariant within = value >= 1 && value <= 10

            data Ok

            behavior f : (n: N) -> Ok
            let f (n) = Ok

            example f
                | "x" : (N(3)) -> Ok
            """;

    /** One type's invariant carried by two behaviors, at a position apiece. */
    private static final String TWO_BEHAVIORS = """
            module example.two

            data UserId = String
                invariant nonempty = String.length(value) >= 1

            data Draft = { owner: UserId }
            data Task = { owner: UserId }

            data Ok

            behavior schedule : (d: Draft) -> Ok
            let schedule (d) = Ok

            behavior touch : (t: Task) -> Ok
            let touch (t) = Ok

            example schedule
                | "a" : (Draft { owner = UserId("x") }) -> Ok

            example touch
                | "a" : (Task { owner = UserId("x") }) -> Ok
            """;

    /** One type's invariant carried twice by one behavior. */
    private static final String TWO_POSITIONS = """
            module example.both

            data UserId = String
                invariant nonempty = String.length(value) >= 1

            data Draft = { owner: UserId, reviewer: UserId }

            data Ok

            behavior schedule : (d: Draft) -> Ok
            let schedule (d) = Ok

            example schedule
                | "a" : (Draft { owner = UserId("x"), reviewer = UserId("y") }) -> Ok
            """;

    /** Two records stopping one type at one value, each by a clause of its own. */
    private static final String TWO_RECORDS = """
            module example.narrow

            data Minute = Int
                invariant range = value >= 0 && value <= 1439

            data Window = { stop: Minute }
                invariant fits = stop.value <= 1000

            data Slot = { at: Minute }
                invariant fits = at.value <= 1000

            data Ok

            behavior w : (x: Window) -> Ok
            let w (x) = Ok

            behavior s : (y: Slot) -> Ok
            let s (y) = Ok

            example w
                | "a" : (Window { stop = Minute(5) }) -> Ok

            example s
                | "a" : (Slot { at = Minute(5) }) -> Ok
            """;

    private static BorderAssessment at(Map<String, BorderAssessment> lines, String label) {
        BorderAssessment line = lines.get(label);
        assertNotNull(line, () -> label + " is not a line of this model: " + lines.keySet());
        return line;
    }

    /** Every border of {@code module}, as the measure holds them: per behavior, and one entry per
     *  occurrence. For a caller counting them rather than looking one up. */
    private static Map<String, List<BorderAssessment>> boundariesOf(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries;
    }

    /** Every border of {@code module}, by the line it is at. Each label names one position, so the
     *  map holds one entry per occurrence and not one per debt. */
    private static Map<String, BorderAssessment> bordersOf(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        Map<String, BorderAssessment> out = new LinkedHashMap<>();
        boundaries.values().forEach(each -> each.forEach(b -> out.put(b.label(), b)));
        return out;
    }
}
