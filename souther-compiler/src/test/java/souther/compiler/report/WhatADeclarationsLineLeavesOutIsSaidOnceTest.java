package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line a declaration drew is the declaration's, in what a report counts and in what it says.
 *
 * <p>{@code Failures} draws a line at 0 and one at 3, and every value of the type is between them.
 * So no row is owed below 0 or above 3, at any position holding a {@code Failures} — which is a fact
 * about the type, said once under the declarations. A behavior's {@code borders} are the lines its
 * own rules drew: {@code greet} compares nothing and has none, and {@code fail} has its own
 * comparison, whose IN point the invariant leaves no value at, and that is a fact about the body.
 */
class WhatADeclarationsLineLeavesOutIsSaidOnceTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module example.login

            data Failures = Int
                invariant value >= 0 && value <= 3
            data Account = { failures: Failures, name: String }

            behavior greet : (account: Account) -> String

            let greet (account) = account.name

            behavior fail : (account: Account) -> Account
                constructs Account, Failures

            let fail (account) =
                if account.failures.value >= 3 then account
                else Account { ...account, failures = Failures(account.failures.value + 1) }

            example greet
                | "a" : (Account { failures = Failures(0), name = "n" }) -> "n"

            example fail
                | "zero" : (Account { failures = Failures(0), name = "n" })
                    -> Account { failures = Failures(1), name = "n" }
                | "two" : (Account { failures = Failures(2), name = "n" })
                    -> Account { failures = Failures(3), name = "n" }
                | "three" : (Account { failures = Failures(3), name = "n" })
                    -> Account { failures = Failures(3), name = "n" }
            """;

    /** What the invariant leaves out, in the words the declarations block says it in. */
    private static final List<String> LEFT_OUT_BY_FAILURES = List.of(
            "· no OFF point is owed at value = 0 (invariant Failures #1): excluded — no value can"
                    + " stand there",
            "· no OUT point is owed at value = 0 (invariant Failures #1): excluded — no value can"
                    + " stand there",
            "· no OFF point is owed at value = 3 (invariant Failures #1): excluded — no value can"
                    + " stand there",
            "· no OUT point is owed at value = 3 (invariant Failures #1): excluded — no value can"
                    + " stand there");

    /** A behavior whose rules compare nothing has no borders, whatever types it carries. */
    @Test
    void aBehaviorThatComparesNothingHasNoBorder() {
        assertEquals(List.of("border      borders 0   obligations 0/0"),
                block(human(compiled(MODEL)), "greet").stream()
                        .filter(each -> each.startsWith("border")).toList());
    }

    /**
     * A behavior's borders are its own rules' lines, and what its own line leaves out is said
     * under it.
     *
     * <p>The IN point of {@code >= 3} is left out because the invariant leaves no value above 3, and
     * it is still news about the body: the comparison is at the type's last value.
     */
    @Test
    void aBehaviorSaysWhatItsOwnLinesLeaveOut() {
        List<String> fail = block(human(compiled(MODEL)), "fail");

        assertTrue(fail.contains("border      borders 1   obligations 3/3"), () -> "" + fail);
        assertEquals(1, fail.stream().filter(each -> each.startsWith("· no ")).count(),
                () -> "the body's one line and nothing of the type's: " + fail);
        assertTrue(fail.stream().anyMatch(each -> each.startsWith(
                        "· no IN point is owed at account.failures = 3 (comparison@")),
                () -> "" + fail);
    }

    /** What the invariant leaves out is said once, under the declarations, and nowhere else. */
    @Test
    void whatTheInvariantLeavesOutIsSaidOnceUnderTheDeclarations() {
        String report = human(compiled(MODEL));
        List<String> declarations = block(report, "declarations");

        assertTrue(declarations.getFirst().startsWith("declarations   borders 2   obligations"),
                () -> "two lines, counted once for the module: " + declarations);
        assertEquals(LEFT_OUT_BY_FAILURES,
                declarations.stream().filter(each -> each.startsWith("· no ")).toList());
        for (String each : LEFT_OUT_BY_FAILURES) {
            assertEquals(1, report.lines().map(String::strip).filter(each::equals).count(),
                    () -> "said once: " + each + "\n" + report);
        }
    }

    /**
     * Two rules at one value are two lines, and what each leaves out is its own.
     *
     * <p>{@code Capped} is written the way {@code Failures} is. Gathered by the value and the role,
     * the two would be one line here and one rule's points would be said under the other's name.
     */
    @Test
    void twoRulesAtOneValueAreTwoLines() {
        List<String> declarations = block(human(compiled(TWO_TYPES)), "declarations");

        assertTrue(declarations.getFirst().startsWith("declarations   borders 4"),
                () -> "" + declarations);
        for (String type : List.of("Failures", "Capped")) {
            assertEquals(4, declarations.stream()
                            .filter(each -> each.startsWith("· no ")
                                    && each.contains("(invariant " + type + " #1)"))
                            .count(),
                    () -> type + " leaves out its own four points: " + declarations);
        }
    }

    /**
     * A view of one behavior says what the lines that behavior reads leave out, and nothing about
     * the lines it does not.
     */
    @Test
    void aViewOfOneBehaviorSaysWhatItsLinesLeaveOut() {
        Compilation compilation = compiled(TWO_TYPES);
        String peek = AdequacyReport.of(compilation).only(null, "peek")
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> declarations = block(peek, "declarations");

        assertTrue(declarations.getFirst().startsWith("declarations   borders 2"),
                () -> "" + declarations);
        assertEquals(LEFT_OUT_BY_FAILURES,
                declarations.stream().filter(each -> each.startsWith("· no ")).toList(),
                "`peek` carries a Failures and no Capped");
    }

    /**
     * One point of one line, owed at one position and left out at another, is two points: the one
     * no row is owed at is told apart by where its region stops.
     *
     * <p>The region above {@code Failures}' line at 0 holds every value above it where a bare
     * {@code Failures} is read, and nothing where {@code Parcel}'s own clause holds the field at 0.
     * So the IN point is owed at {@code b} and left out at {@code a}: one line, read two ways, and
     * both readings are right. The point below the line is left out by the bound alone, wherever
     * the type is read, and is said with nothing after the rule.
     */
    @Test
    void aPointLeftOutWhereARecordEmptiesTheRegionIsToldApartByWhereItStops() {
        Compilation compilation = compiled(NARROWED);
        List<String> declarations = block(human(compilation), "declarations");

        assertTrue(declarations.contains("· no IN point is owed at value = 0 (invariant Failures #1"
                        + " where the values stop at 0): excluded — no value can stand there"),
                () -> "" + declarations);
        assertTrue(declarations.contains("? undecided whether a row is at the IN point value in"
                        + " 0 < value (invariant Failures #1) — no row names this behavior"),
                () -> "and the same role of the same line, where nothing stops the region, is owed: "
                        + declarations);
        assertTrue(declarations.contains("· no OFF point is owed at value = 0 (invariant Failures"
                        + " #1): excluded — no value can stand there"),
                () -> "below the line nothing is a Failures wherever it is read: " + declarations);

        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<String> stops = new ArrayList<>();
        document.get("modules").get(0).get("declarations").forEach(entry ->
                entry.get("excluded").forEach(each -> each.get("pointId").get("stops")
                        .forEach(at -> stops.add(each.get("point").asString() + " "
                                + at.get("kind").asString()))));
        assertEquals(List.of("in at_the_domain", "in at_the_domain"), stops,
                "the IN point of each line at 0 is left out where the values stop, and nothing"
                        + " else is settled anywhere but by its own line");
        DocumentShape.assertShapedLikeTheSchema(document);
    }

    /**
     * What the declarations say does not turn on the order the behaviors reading their lines are
     * declared in.
     *
     * <p>Every reading of one point is one point and is gathered whole, so which behavior met it
     * first decides nothing about it.
     */
    @Test
    void whatTheDeclarationsSayDoesNotTurnOnTheOrderOfTheBehaviors() {
        List<String> declaredFirst = block(human(compiled(NARROWED)), "declarations");
        List<String> declaredSecond = block(human(compiled(NARROWED.replace("""
                behavior a : (p: Parcel) -> Int
                let a (p) = 1

                behavior b : (f: Failures) -> Int
                let b (f) = 1
                """, """
                behavior b : (f: Failures) -> Int
                let b (f) = 1

                behavior a : (p: Parcel) -> Int
                let a (p) = 1
                """))), "declarations");

        assertFalse(declaredFirst.isEmpty(), "the model draws lines");
        assertEquals(Set.copyOf(withoutReadings(declaredFirst)),
                Set.copyOf(withoutReadings(declaredSecond)),
                () -> declaredFirst + "\n" + declaredSecond);
    }

    /** The lines of a block that say what a point is, without the readings listed under them,
     *  whose order is the order the behaviors are in. */
    private static List<String> withoutReadings(List<String> block) {
        return block.stream().filter(each -> !each.startsWith("· read as ")).toList();
    }

    private static final String NARROWED = """
            module example.narrowed

            data Failures = Int
                invariant value >= 0
            data Parcel = { failures: Failures }
                invariant failures.value <= 0

            behavior a : (p: Parcel) -> Int
            let a (p) = 1

            behavior b : (f: Failures) -> Int
            let b (f) = 1
            """;

    private static final String TWO_TYPES = """
            module example.two

            data Failures = Int
                invariant value >= 0 && value <= 3
            data Capped = Int
                invariant value >= 0 && value <= 3
            data Account = { failures: Failures, capped: Capped, name: String }
            data Other = { failures: Failures }

            behavior greet : (account: Account) -> String

            let greet (account) = account.name

            behavior peek : (other: Other) -> Int

            let peek (other) = other.failures.value

            example greet
                | "a" : (Account { failures = Failures(0), capped = Capped(0), name = "n" }) -> "n"

            example peek
                | "a" : (Other { failures = Failures(1) }) -> 1
            """;

    /**
     * The document says each point once, under the declaration, and keeps the readings it has
     * always published.
     *
     * <p>A behavior's {@code boundaries} are every line as its positions met it, which is what an
     * entry about a line of a type read at one position joins to; the declaration's account of what
     * its lines leave out is beside them and is not a second copy of them per behavior.
     */
    @Test
    void theDocumentSaysEachPointOnceUnderTheDeclarations() {
        Compilation compilation = compiled(MODEL);
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        JsonNode module = document.get("modules").get(0);

        List<JsonNode> excluded = new ArrayList<>();
        module.get("declarations").forEach(each -> each.get("excluded").forEach(excluded::add));
        assertEquals(List.of("off value = 0", "out value = 0", "off value = 3", "out value = 3"),
                excluded.stream().map(each -> each.get("point").asString() + " "
                        + each.get("label").asString()).toList());
        assertEquals(excluded.size(), new LinkedHashSet<>(excluded.stream()
                        .map(each -> each.get("pointId")).toList()).size(),
                () -> "each point is one entry: " + excluded);

        List<JsonNode> read = new ArrayList<>();
        for (JsonNode behavior : module.get("behaviors")) {
            if ("fail".equals(behavior.get("name").asString())) {
                behavior.get("partition").get("boundaries").forEach(
                        each -> read.add(each.get("lineId")));
            }
        }
        assertEquals(3, read.size(),
                () -> "the two lines of the type and the body's own, as `fail` met them: " + read);
        DocumentShape.assertShapedLikeTheSchema(document);
    }

    /** The lines of one block of the report, stripped: a behavior's, or the declarations'. */
    private static List<String> block(String report, String heading) {
        List<String> out = new ArrayList<>();
        boolean in = false;
        for (String line : report.lines().toList()) {
            boolean headingLine = line.startsWith("  ") && !line.startsWith("    ");
            if (headingLine) {
                in = line.strip().startsWith(heading + " ")
                        || line.strip().equals(heading);
            }
            if (in && !line.isBlank()) {
                out.add(line.strip());
            }
        }
        assertTrue(!out.isEmpty(), () -> "the report has a block for " + heading + ":\n" + report);
        return out;
    }

    private static String human(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * Each model measured once for the class. The checks only read what a compilation answers, and
     * the database keeps the answers, so several checks asking it is one measurement asked again.
     */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation compiled(String source) {
        return MEASURED.computeIfAbsent(source, each -> {
            Compilation compilation = Compilation.ofSource(each, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertTrue(compilation.errors().isEmpty(), () -> "the model compiles: "
                    + compilation.errors());
            return compilation;
        });
    }
}
