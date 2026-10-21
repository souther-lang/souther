package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BinaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A map a fold builds by adding what each element holds, or keeping an end of it, under the key of
 * the element, looked up under a key another parameter holds: what the lookup finds is what the
 * elements of that key come to, and the arm finding something is taken exactly where some element
 * has the key.
 */
class ATotalLookedUpUnderAKeyAskedForIsReadAsTheElementsOfThatKeyTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String ADDING =
            "Map.updateOrInsert(p.account, p.amount, n -> n + p.amount, acc)";

    private static final String LEAST =
            "Map.updateOrInsert(p.account, p.amount, n -> Int.min(n, p.amount), acc)";

    private record Posting(String account, int amount) {

        String written() {
            return "Posting { account = \"" + account + "\", amount = " + amount + " }";
        }
    }

    /** One row offered for {@code large}: the postings of each list, in order, and the key. */
    private record Row(List<List<Posting>> lists, String account) {

        /** What the lookup finds, or null where no element has the key. */
        Integer found(BinaryOperator<Integer> gathered) {
            Integer found = null;
            for (List<Posting> list : lists) {
                for (Posting each : list) {
                    if (each.account().equals(account)) {
                        found = found == null ? each.amount() : gathered.apply(found, each.amount());
                    }
                }
            }
            return found;
        }

        /** Whether the lookup finds something and what it finds is at least a hundred. */
        boolean large(BinaryOperator<Integer> gathered) {
            Integer found = found(gathered);
            return found != null && found >= 100;
        }
    }

    /**
     * What the key asked for is: a string, or a name of at least two characters. The elements'
     * keys are strings, so they do not stand at the key asked for unless the row writes them there
     * — where the key is a string, the empty one is what each holds when nothing says otherwise,
     * and the two would be one value without the row doing anything.
     */
    private enum Keys {
        ANY("", "String", "account", "\"%s\""),
        A_NAME("""
                data Account = String
                    invariant String.length(value) >= 2

                """, "Account", "account.value", "Account(\"%s\")");

        private final String declaration;
        private final String type;
        private final String read;
        private final String written;

        Keys(String declaration, String type, String read, String written) {
            this.declaration = declaration;
            this.type = type;
            this.read = read;
            this.written = written;
        }

        /** The key {@code name} as a row writes it. */
        String written(String name) {
            return written.formatted(name);
        }
    }

    private static String overOneList(String step, String more) {
        return overOneList(Keys.ANY, step, more);
    }

    private static String overTheLists(String step, String more) {
        return overTheLists(Keys.ANY, step, more);
    }

    private static String overOneList(Keys keys, String step, String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                %slet totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior large : (ps: List<Posting>, account: %s) -> Bool

                let large (ps, account) =
                    match Map.get(%s, totals(ps)) with
                        | Some amount -> amount >= 100
                        | None -> false
                %s""".formatted(keys.declaration, step, keys.type, keys.read, more);
    }

    private static String overTheLists(Keys keys, String step, String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Entry = { postings: List<Posting> }

                %slet totals (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty,
                              List.flatMap(e -> e.postings, entries))

                behavior large : (entries: List<Entry>, account: %s) -> Bool

                let large (entries, account) =
                    match Map.get(%s, totals(entries)) with
                        | Some amount -> amount >= 100
                        | None -> false
                %s""".formatted(keys.declaration, step, keys.type, keys.read, more);
    }

    @Test
    void aTotalLookedUpUnderAKeyAskedForIsTheTotalOfTheElementsOfThatKey() {
        Compilation compilation = measured(overOneList(ADDING, ""));
        assertTrue(json(compilation).contains("gathered_under_a_key"), () -> report(compilation));
        assertTrue(json(compilation).contains("total(ps[*].amount by account) equal to account"),
                () -> report(compilation));
    }

    @Test
    void theDocumentNamingItIsOneTheSchemaAccepts() {
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                overOneList(ADDING, "")))));
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                overTheLists(ADDING, "")))));
    }

    /**
     * What another key's elements hold is no part of the total of this one: a row of 60 and 40
     * under one account with 900 under another is at the point of a hundred for the first, and one
     * with 39 for the 40 is at the point below it, whatever the second holds.
     */
    @Test
    void theElementsOfOtherKeysAreNoPartOfTheTotal() {
        String examples = """

                example large
                    | "on" : (%1$s, "A") -> true
                    | "off" : (%2$s, "A") -> false
                    | "absent" : (%1$s, "C") -> false
                """.formatted(
                postings(new Posting("A", 60), new Posting("B", 900), new Posting("A", 40)),
                postings(new Posting("A", 60), new Posting("B", 900), new Posting("A", 39)));
        List<String> unmet = unmetOf(measured(overOneList(ADDING, examples)));
        assertFalse(unmet.contains("ON"), () -> "the point of a hundred is met: " + unmet);
        assertFalse(unmet.contains("OFF"), () -> "the point below it is met: " + unmet);
    }

    /**
     * A key whose elements add up to nought is a key some element has: the lookup finds nought,
     * which is not what a key no element has finds.
     */
    @Test
    void aTotalOfNoughtIsFoundAndAKeyNoElementHasIsNot() {
        String model = overOneList(ADDING, "").replace("amount >= 100", "amount >= 0");
        String examples = """

                example large
                    | "found" : (%s, "A") -> true
                    | "below" : (%s, "A") -> false
                    | "absent" : (%s, "B") -> false
                """.formatted(
                postings(new Posting("A", 100), new Posting("A", -100)),
                postings(new Posting("A", 100), new Posting("A", -101)),
                postings(new Posting("A", 0)));
        Compilation compilation = measured(model + examples);
        List<String> unmet = unmetOf(compilation);
        assertFalse(unmet.contains("ON"), () -> "nought is the point: " + report(compilation));
        assertFalse(unmet.contains("OFF"), () -> "below nought is met: " + report(compilation));
    }

    private static String postings(Posting... each) {
        return List.of(each).stream().map(Posting::written).toList().toString();
    }

    @Test
    void aLineOnTheTotalOfAKeyAskedForIsOwedOfferedAndThenMet() {
        for (Keys keys : Keys.values()) {
            assertTheLineIsOfferedAndMet(keys, false, ADDING, Integer::sum);
        }
    }

    @Test
    void aLineOnTheTotalAcrossTheListsIsOwedOfferedAndThenMet() {
        for (Keys keys : Keys.values()) {
            assertTheLineIsOfferedAndMet(keys, true, ADDING, Integer::sum);
        }
    }

    @Test
    void aLineOnTheLeastOfAKeyAskedForIsOwedOfferedAndThenMet() {
        for (Keys keys : Keys.values()) {
            assertTheLineIsOfferedAndMet(keys, false, LEAST, Math::min);
        }
    }

    @Test
    void aLineOnTheLeastAcrossTheListsIsOwedOfferedAndThenMet() {
        for (Keys keys : Keys.values()) {
            assertTheLineIsOfferedAndMet(keys, true, LEAST, Math::min);
        }
    }

    private static void assertTheLineIsOfferedAndMet(Keys keys, boolean acrossTheLists,
                                                     String step,
                                                     BinaryOperator<Integer> gathered) {
        String examples = """

                example large
                    | "none" : ([], %s) -> false
                """.formatted(keys.written("AB"));
        String model = acrossTheLists ? overTheLists(keys, step, examples)
                : overOneList(keys, step, examples);
        Compilation before = measured(model);
        List<String> owed = unmetOf(before);
        assertFalse(owed.isEmpty(), () -> "the line is owed its points: " + report(before));
        List<Row> offered = offeredRows(before, acrossTheLists);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        // The line is drawn at a hundred of what the key's elements come to, so rows stand on
        // both sides of it by that number and by no other.
        for (int at : new int[] {99, 100}) {
            assertTrue(offered.stream().anyMatch(row -> Integer.valueOf(at)
                    .equals(row.found(gathered))), () -> "a row finds " + at + ": " + offered);
        }
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(writtenAs(keys, row, acrossTheLists)).append(") -> ")
                    .append(row.large(gathered)).append("\n");
        }
        Compilation after = measured(acrossTheLists ? overTheLists(keys, step, written.toString())
                : overOneList(keys, step, written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
        assertFalse(report(after).contains("no row takes a decision rule"),
                () -> "the arm finding something and the arm finding nothing are both taken: "
                        + report(after));
    }

    private static String writtenAs(Keys keys, Row row, boolean acrossTheLists) {
        List<String> lists = new ArrayList<>();
        for (List<Posting> list : row.lists()) {
            String postings = list.stream().map(Posting::written).toList().toString();
            lists.add(acrossTheLists ? "Entry { postings = " + postings + " }" : postings);
        }
        String written = acrossTheLists ? lists.toString() : lists.getFirst();
        return written + ", " + keys.written(row.account());
    }

    private static final Pattern ROW =
            Pattern.compile("^(.*), (?:Account\\()?\"((?:[^\"\\\\]|\\\\.)*)\"\\)?$");

    private static final Pattern POSTING = Pattern.compile(
            "Posting \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\", amount = (-?\\d+) \\}");

    private static final Pattern ENTRY = Pattern.compile("Entry \\{ postings = \\[(.*?)\\] \\}");

    private static List<Row> offeredRows(Compilation compilation, boolean acrossTheLists) {
        List<Row> out = new ArrayList<>();
        for (String each : offeredInputs(compilation)) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            String written = matched.group(1);
            List<List<Posting>> lists = new ArrayList<>();
            if (acrossTheLists) {
                Matcher entry = ENTRY.matcher(written);
                while (entry.find()) {
                    lists.add(postingsIn(entry.group(1)));
                }
                if (lists.isEmpty() && !written.equals("[]")) {
                    fail("the entries of an offered row are read back: " + written);
                }
            } else {
                lists.add(postingsIn(written.substring(1, written.length() - 1)));
            }
            out.add(new Row(lists, matched.group(2)));
        }
        return out;
    }

    private static List<Posting> postingsIn(String list) {
        List<Posting> postings = new ArrayList<>();
        Matcher one = POSTING.matcher(list);
        StringBuilder rest = new StringBuilder();
        while (one.find()) {
            postings.add(new Posting(one.group(1), Integer.parseInt(one.group(2))));
            one.appendReplacement(rest, "");
        }
        one.appendTail(rest);
        if (!rest.toString().replace(",", "").isBlank()) {
            fail("the postings of an offered row are read to the end: " + list);
        }
        return postings;
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.ledger"))
                .rowsByBehavior().getOrDefault("large", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** The points of the lines drawn that no row is at, by name. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static final Pattern POINT = Pattern.compile("^(ON|OFF|IN|OUT) point of ");

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("findings")) {
            node.path("findings").forEach(finding -> {
                Matcher point = POINT.matcher(finding.path("subject").asString());
                if (point.find()) {
                    out.add(point.group(1));
                }
            });
        }
        node.forEach(child -> unmet(child, out));
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
