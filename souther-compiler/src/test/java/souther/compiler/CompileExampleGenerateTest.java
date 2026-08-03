package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows generated against a model that really compiles, and put through the decoders that model derives.
 *
 * <p>Which is the part a generator cannot work out on its own. Whether two values are allowed together
 * is what an invariant relating two fields says, and the only way to find out is to build the value the
 * way a row's own fixture is built.
 */
class CompileExampleGenerateTest {

    private static final String TRIP = """
            module example.trip

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Request = { kind: Kind, urgent: Bool }

            data Accepted = { at: String }

            behavior submit : (request: Request) -> Accepted
                constructs Accepted

            let submit (request) = Accepted { at = "now" }

            example submit
                | (Request { kind = Domestic, urgent = true }) -> Accepted { at = "now" }
            """;

    private static Map<String, Adequacy.Filling> generated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        // What `souther examples` asks for. A line a `guard` drew is only decidable where the arms
        // were measured, so below this the generator has nothing to say about one.
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all;
    }

    private static List<String> inputs(Generator.GenerationResult result) {
        return result.rows().stream()
                .map(r -> String.join(", ",
                        r.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }

    @Test
    void whatTheWrittenRowAlreadyCoversIsNotGeneratedAgain() {
        Generator.GenerationResult filled = generated(TRIP).get("submit").pairs();

        assertEquals(List.of(
                        "Request { kind = Domestic, urgent = false }",
                        "Request { kind = Overseas, urgent = true }",
                        "Request { kind = Overseas, urgent = false }"),
                inputs(filled));
        assertEquals(List.of(), filled.unresolved());
    }

    /**
     * A rule relating two fields refuses a value each field would have allowed on its own.
     *
     * <p>Here the low end may not be above the high end. Each position on its own admits the values
     * that break it — the classes are drawn by the behavior's own comparisons and know nothing of each
     * other — so the only thing that can say the pair is not allowed is the decoder the model derives.
     * What comes back is the reason it was refused, not a claim that the combination is impossible.
     */
    @Test
    void aRuleRelatingTwoFieldsRefusesTheValueAndIsSaidSo() {
        String correlated = """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Request = { lo: Amount, hi: Amount }
                    invariant lo.value <= hi.value

                data Accepted = { at: String }

                behavior submit : (request: Request) -> Accepted
                    constructs Accepted

                let submit (request) = {
                    guard request.lo.value <= 100 else Accepted { at = "wide" }
                    guard request.hi.value <= 50 else Accepted { at = "tall" }
                    Accepted { at = "now" }
                }
                """;
        Generator.GenerationResult filled = generated(correlated).get("submit").pairs();

        assertTrue(inputs(filled).stream().noneMatch(row -> row.contains("Amount(101)")),
                "a value the model refuses is not written into a row: " + inputs(filled));
        // Both combinations the low end's upper class takes part in, and the class on its own.
        assertEquals(3, filled.unresolved().size(), filled.unresolved().toString());
        for (Generator.UnresolvedCombination left : filled.unresolved()) {
            assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                    left.reason());
            assertTrue(left.classes().contains("request.lo=100 < x"),
                    left.classes().toString());
        }
        // The second of the two is the reason this reason exists. A low end past 100 and a high end
        // past 50 is a combination values exist for — 101 and 200 — and the representatives the
        // classes offered happened not to be a pair that builds. Calling that impossible would take a
        // combination somebody can write a row for out of the denominator.
        assertTrue(filled.unresolved().stream()
                        .anyMatch(left -> left.classes().contains("request.hi=50 < x")),
                filled.unresolved().toString());
    }

    /**
     * A boundary is a row of its own, apart from the rows that fill the classes.
     *
     * <p>The two ask different things. A class wants any value inside it; an edge wants exactly the
     * value the rule was written at, and a row that sat on three edges at once would be three answers
     * an author has to separate.
     */
    @Test
    void aBoundaryNothingReachedGetsARowOfItsOwn() {
        String bounded = """
                module example.trip

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Request = { kind: Kind, cost: Amount }

                data Accepted = { at: String }

                behavior submit : (request: Request) -> Accepted
                    constructs Accepted

                let submit (request) = Accepted { at = "now" }
                """;
        Adequacy.Filling filling = generated(bounded).get("submit");

        assertEquals(List.of("Request { kind = Domestic, cost = Amount(0) }",
                        "Request { kind = Overseas, cost = Amount(0) }"),
                inputs(filling.pairs()), "the classes, at whatever cost builds");
        assertEquals(List.of("Request { kind = Domestic, cost = Amount(0) }",
                        "Request { kind = Domestic, cost = Amount(1000) }"),
                inputs(filling.boundaries()), "the edges, at exactly the value the rule names");
    }

    /**
     * A line a `guard` drew is offered, not only named.
     *
     * <p>Writing the row and meeting the line are different questions, and only the second needs the
     * arms — but the row to write is the same row either way. A boundary the report names as unmet and
     * the generator will not offer is the one place an author is told about a gap and left to close it
     * by hand.
     */
    @Test
    void aGuardsLineIsOfferedAsWellAsNamed() {
        String guarded = """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Draft = { cost: Amount }
                data Submitted = { cost: Amount }
                data Waiting = { cost: Amount }

                behavior submit : (request: Draft) -> Submitted | Waiting
                    constructs Submitted, Waiting

                let submit (request) = {
                    guard request.cost.value <= 100 else Waiting { cost = request.cost }
                    Submitted { cost = request.cost }
                }

                example submit
                    | (Draft { cost = Amount(50) })  -> Submitted { cost = Amount(50) }
                    | (Draft { cost = Amount(500) }) -> Waiting { cost = Amount(500) }
                """;

        assertEquals(List.of("Draft { cost = Amount(0) }",
                        "Draft { cost = Amount(100) }",
                        "Draft { cost = Amount(101) }"),
                inputs(generated(guarded).get("submit").boundaries()),
                "the invariant's edge and both sides of the guard's line");
    }

    /**
     * A value a format rule accepts, and one the model then builds.
     *
     * <p>An identifier saying what it looks like is the commonest rule there is, and nothing could
     * write one — so a record holding an id could not be composed at all, and every combination that
     * record took part in came back as one whose values the model refused. What settles this is not
     * that the string looks right but that the derived decoder takes it, which is what the check here
     * is: the row is offered only if it built.
     */
    @Test
    void anIdentifierWithAFormatRuleGetsAValueTheModelAccepts() {
        String formatted = """
                module example.office

                data OfficeId = String
                    invariant String.matches("[0-9]{2}-[0-9]{6}", value)

                data Prefecture = String
                    invariant String.matches("0[1-9]|[1-3][0-9]|4[0-7]", value)

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Office = { id: OfficeId, prefecture: Prefecture, kind: Kind }
                data Ok = { n: Int }

                behavior register : (office: Office) -> Ok
                    constructs Ok

                let register (office) = Ok { n = 0 }

                example register
                    | (Office { id = OfficeId("12-345678"), prefecture = Prefecture("13"),
                                kind = Domestic }) -> Ok { n = 0 }
                """;

        assertEquals(List.of(
                        "Office { id = OfficeId(\"00-000000\"), prefecture = Prefecture(\"01\"),"
                                + " kind = Overseas }"),
                inputs(generated(formatted).get("register").pairs()),
                "the class nothing covers, with an id and a prefecture the rules accept");
    }

    /** And a date, which a row writes as its ISO form. */
    @Test
    void aDateGetsAValueTheModelAccepts() {
        String dated = """
                module example.dated

                data Yes
                data No
                data Flag = Yes | No

                data Request = { on: Date, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Request) -> Ok
                    constructs Ok

                let take (request) = Ok { n = 0 }

                example take
                    | (Request { on = Date("2026-08-03"), flag = Yes }) -> Ok { n = 0 }
                """;

        assertEquals(List.of("Request { on = Date(\"2000-01-01\"), flag = No }"),
                inputs(generated(dated).get("take").pairs()));
    }

    // --- the block, put back through the compiler ------------------------------------------------

    /** The rows of the block, with the placeholder answered the way an author answers it. */
    private static String answered(String source, String expected) {
        String block = GeneratedRows.of("example.trip", generated(source), false);
        String rows = block.lines()
                .filter(line -> line.startsWith("//     ") || line.equals("// example submit"))
                .map(line -> line.substring("// ".length()).replace("<?>", expected))
                .reduce("", (all, line) -> all + line + "\n");
        return source + rows;
    }

    /** The rows a source's examples left, across every file that writes one. */
    private static List<souther.compiler.observe.RowOutcome> outcomes(Compilation compilation) {
        List<souther.compiler.observe.RowOutcome> rows = new ArrayList<>();
        for (String name : compilation.modules()) {
            for (String sourceId : compilation.exampleSourcesOf(name)) {
                souther.compiler.query.Output.Examples.Of observed = compilation.db()
                        .ask(new souther.compiler.query.Output.Examples(name, sourceId)).value();
                if (observed != null) {
                    rows.addAll(observed.rows());
                }
            }
        }
        return rows;
    }

    /**
     * Answered, the block is rows that hold, and what they were generated for is covered.
     *
     * <p>The whole claim about a generated row, put to the compiler rather than to the text: it parses,
     * the inputs build, the behavior takes them, the answer written against them is the one it gives,
     * and afterwards there is nothing left to generate. A row that only looked right would pass none of
     * those.
     */
    @Test
    void answeringTheBlockGivesRowsThatHoldAndCoverWhatTheyWereFor() {
        String source = answered(TRIP, "Accepted { at = \"now\" }");

        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        List<souther.compiler.observe.RowOutcome> rows = outcomes(compilation);

        assertEquals(4, rows.size(), "the row that was there, and the three generated");
        for (souther.compiler.observe.RowOutcome row : rows) {
            assertEquals(souther.compiler.observe.Disposition.HELD, row.disposition(),
                    row.description() + " -> " + row.failurePhase());
        }
        assertEquals("", GeneratedRows.of("example.trip", generated(source), false),
                "nothing is left to fill");
    }

    /** And the check above is not vacuous: a row answered with something the behavior does not give
     * fails, so the rows holding is the block's doing and not the compiler's indifference. */
    @Test
    void aRowAnsweredWrongDoesNotHold() {
        String wrong = answered(TRIP, "Accepted { at = \"later\" }");

        Compilation compilation = Compilation.ofSource(wrong, "Main");
        compilation.answerEverything();

        assertTrue(outcomes(compilation).stream()
                        .anyMatch(row -> row.disposition() == souther.compiler.observe.Disposition
                                .FAILED),
                "a wrong answer is a failing row");
    }

    /**
     * Pasted as it comes, the block changes nothing.
     *
     * <p>Which is what being commented out means, said as something the compiler can answer. A row that
     * compiled would be an assertion nobody made, and the next build would hold the model to it.
     */
    @Test
    void theBlockPastedUnchangedLeavesTheModelWhereItWas() {
        String block = GeneratedRows.of("example.trip", generated(TRIP), false);
        String pasted = TRIP + block;

        Compilation compilation = Compilation.ofSource(pasted, "Main");
        compilation.answerEverything();

        assertEquals(1, outcomes(compilation).size(), "no row was added");
        assertEquals(block, GeneratedRows.of("example.trip", generated(pasted), false),
                "the same rows are still owed");
    }

    /**
     * The rows come out in the form {@code souther fmt} writes them.
     *
     * <p>These lines are meant to be pasted into a file the formatter then runs over. A block in a
     * shape the formatter would change turns a paste into a diff on the next commit.
     */
    @Test
    void thePastedRowsSurviveFormattingUnchanged() {
        String source = answered(TRIP, "Accepted { at = \"now\" }");
        String formatted = souther.compiler.fmt.Formatter.format(source);

        for (String line : source.substring(TRIP.length()).lines().toList()) {
            assertTrue(formatted.contains(line + "\n"), line + "\n---\n" + formatted);
        }
    }

    /** Nothing to fill is nothing printed, rather than a header over an empty list. */
    @Test
    void aModelTheRowsCoverPrintsNothing() {
        String covered = TRIP + """
                    | (Request { kind = Domestic, urgent = false }) -> Accepted { at = "now" }
                    | (Request { kind = Overseas, urgent = true }) -> Accepted { at = "now" }
                    | (Request { kind = Overseas, urgent = false }) -> Accepted { at = "now" }
                """;

        assertEquals("", GeneratedRows.of("example.trip", generated(covered), false));
    }
}
