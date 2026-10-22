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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.function.UnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A map a fold builds by adding what each element holds to what was filed under its key holds
 * under a key the total of what the elements of that key hold — so a statement about one of its
 * values is a statement about that total, and a row is composed on each side of it.
 *
 * <p>Not a statement about any one element. Of two elements of one key holding four and ten, the
 * total is fourteen, which neither holds. And the elements of a key are gathered from every list
 * a fold over the lists of an outer list put end to end walks, so two of one key in two lists are
 * one total.
 */
class AFoldThatAddsWhatEachKeyFilesAnswersTheTotalOfItsValuesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String ADDING =
            "Map.updateOrInsert(p.account, p.amount, on -> on + p.amount, acc)";

    /** One line of an account, on a side where the model has one: null where it has none. */
    private record Posting(String account, String side, int amount) {

        Posting(String account, int amount) {
            this(account, null, amount);
        }

        /** What the line comes to: its amount, taken off on the credit side. */
        int signed() {
            return "Credit".equals(side) ? -amount : amount;
        }

        String written() {
            return "Posting { account = \"" + account + "\""
                    + (side == null ? "" : ", side = " + side) + ", amount = " + amount + " }";
        }
    }

    /** One row offered for {@code over}: the postings, each list of an outer list in order, and
     *  the limit. */
    private record Row(List<List<Posting>> lists, int limit) {

        /** What the fold files under each account, gathering two values by {@code gathered}. */
        Map<String, Integer> filed(BinaryOperator<Integer> gathered) {
            Map<String, Integer> out = new LinkedHashMap<>();
            for (List<Posting> list : lists) {
                for (Posting each : list) {
                    out.merge(each.account(), each.signed(), gathered);
                }
            }
            return out;
        }

        /** The entries the filter keeps. */
        Map<String, Integer> kept(BinaryOperator<Integer> gathered) {
            Map<String, Integer> out = new LinkedHashMap<>();
            filed(gathered).forEach((account, amount) -> {
                if (amount >= limit) {
                    out.put(account, amount);
                }
            });
            return out;
        }
    }

    /** A model over one list of postings, filing them by {@code step}. */
    private static String overOneList(String step, String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let netOf (postings: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, postings)

                behavior over : (postings: List<Posting>, limit: Int) -> Map<String, Int>

                let over (postings, limit) =
                    Map.filterEntries((_, net) -> net >= limit, netOf(postings))
                %s""".formatted(step, more);
    }

    /** The same over the lists of the entries put end to end. */
    private static String overTheLists(String step, String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Entry = { postings: List<Posting> }

                let netOf (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, List.flatMap(e -> e.postings, entries))

                behavior over : (entries: List<Entry>, limit: Int) -> Map<String, Int>

                let over (entries, limit) =
                    Map.filterEntries((_, net) -> net >= limit, netOf(entries))
                %s""".formatted(step, more);
    }

    @Test
    void aLineOnTheTotalOfAKeysValuesIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(false, examples -> overOneList(ADDING, examples),
                Integer::sum, "total(postings[*].amount by account)");
    }

    /** Elements of one key in two lists of the outer list are one total. */
    @Test
    void aLineOnTheTotalAcrossTheListsIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(true, examples -> overTheLists(ADDING, examples),
                Integer::sum, "total(entries[*].postings[*].amount by account)");
    }

    /** The least of a key's values across the lists is the end of what every list holds of it. */
    @Test
    void aLineOnTheLeastAcrossTheListsIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(true, examples -> overTheLists(
                "Map.updateOrInsert(p.account, p.amount, on -> Int.min(on, p.amount), acc)",
                examples), Math::min, "least(entries[*].postings[*].amount by account)");
    }

    /**
     * A number a helper makes of each element by the case of a place beside the one it reads — a
     * line's amount, taken off on the credit side — totalled under the key across the lists: the
     * line is on that total, and the rows offered for it are of the case each arm takes.
     */
    @Test
    void aLineOnTheTotalOfWhatAHelperMakesOfEachElementIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(true, examples -> signedOverTheLists(Int.ANY, examples),
                Integer::sum, SIGNED);
    }

    /**
     * And a line only the other arm reaches: amounts are never negative and the line is below
     * nought, so every row at it holds a credit, which is written as one.
     */
    @Test
    void aLineOnlyTheCreditSideReachesIsMetByRowsOfThatSide() {
        assertTheLineIsOfferedAndMet(true, examples -> signedOverTheLists(Int.BELOW_NOUGHT,
                examples), Integer::sum, SIGNED, Int.BELOW_NOUGHT);
    }

    private static final String SIGNED = "total({when side@Debit then 1·amount + 0 when"
            + " side@Credit then -1·amount + 0 | entries[*].postings[*]} by account)";

    /** What the limit is, and how one is written. */
    private enum Int {
        ANY("Int", "limit"),
        BELOW_NOUGHT("Floor", "limit.value");

        private final String type;
        private final String read;

        Int(String type, String read) {
            this.type = type;
            this.read = read;
        }

        String written(int limit) {
            return this == ANY ? String.valueOf(limit) : "Floor(" + limit + ")";
        }
    }

    /** A model whose fold adds what {@code signed} makes of each posting of every entry. */
    private static String signedOverTheLists(Int limit, String more) {
        return """
                module example.ledger

                data Side = Debit | Credit

                data Posting = { account: String, side: Side, amount: Int }
                    invariant %3$s

                data Entry = { postings: List<Posting> }

                data Floor = Int
                    invariant value < 0

                let signed (p: Posting): Int =
                    match p.side with
                        | Debit -> p.amount
                        | Credit -> 0 - p.amount

                let netOf (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, signed(p),
                                              on -> on + signed(p), acc),
                              Map.empty, List.flatMap(e -> e.postings, entries))

                behavior over : (entries: List<Entry>, limit: %1$s) -> Map<String, Int>

                let over (entries, limit) =
                    Map.filterEntries((_, net) -> net >= %2$s, netOf(entries))
                %4$s""".formatted(limit.type, limit.read,
                limit == Int.ANY ? "String.length(account) >= 0" : "amount >= 0", more);
    }

    private static void assertTheLineIsOfferedAndMet(boolean acrossTheLists,
                                                     UnaryOperator<String> model,
                                                     BinaryOperator<Integer> gathered,
                                                     String axis) {
        assertTheLineIsOfferedAndMet(acrossTheLists, model, gathered, axis, Int.ANY);
    }

    private static void assertTheLineIsOfferedAndMet(boolean acrossTheLists,
                                                     UnaryOperator<String> model,
                                                     BinaryOperator<Integer> gathered,
                                                     String axis, Int limit) {
        String examples = """

                example over
                    | "none" : ([], %s) -> []
                """.formatted(limit.written(-2));
        Compilation before = measured(model.apply(examples));
        assertTrue(json(before).contains(axis), () -> "the line is on " + axis + ": "
                + report(before));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));

        List<Row> offered = offeredRows(before, acrossTheLists);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(writtenAs(row, acrossTheLists, limit)).append(") -> ")
                    .append(entries(row.kept(gathered))).append("\n");
        }
        Compilation after = measured(model.apply(written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * What a key's elements come to is read where the run answers, and whether it answers is the
     * run's: a row whose run stops — making one element's number, or at a sum on the way past the
     * last number an {@code Int} holds, in the order the walk hands the elements — stands at no
     * point, though what its elements come to is the number the point is at. The same elements
     * walked the other way round answer, and stand there.
     */
    @Test
    void aRowWhoseRunStopsStandsAtNoPointWhateverItsElementsComeTo() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let netOf (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, p.amount,
                                              n -> n + %s, acc), Map.empty, %s)

                behavior over : (ps: List<Posting>, limit: Int) -> Map<String, Int>

                let over (ps, limit) = Map.filterEntries((_, t) -> t >= limit, netOf(ps))

                example over
                    | "row" : (%s, 9223372036854775807) -> [("a", 9223372036854775807)]
                """;
        String last = String.valueOf(Long.MAX_VALUE);
        String passing = List.of(posting(last), posting("1"), posting("-1")).toString();
        for (String stops : List.of(
                model.formatted("(p.amount + 1 - 1)", "ps",
                        List.of(posting("0"), posting(last)).toString()),
                model.formatted("p.amount", "ps", passing))) {
            Compilation compilation = ran(stops);
            assertTrue(unmetOf(compilation).contains("ON"),
                    () -> "a row whose run stops is at no point: " + report(compilation));
        }
        Compilation reversed = ran(model.formatted("p.amount", "List.reverse(ps)", passing));
        assertFalse(unmetOf(reversed).contains("ON"),
                () -> "the same elements walked the other way round answer: " + report(reversed));
    }

    private static String posting(String amount) {
        return "Posting { account = \"a\", amount = " + amount + " }";
    }

    /** The source measured, whose examples may stop where they run. */
    private static Compilation ran(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * A record a map takes out of each element, the value standing at a place of it, is totalled
     * where it stands, in one list and across the lists of an outer list alike — as a counter over
     * the same walk counts its key there.
     */
    @Test
    void aRecordAMapTakesOutOfEachElementIsTotalledWhereItStands() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Entry = { inner: Posting, note: String }

                let netOf (src: %1$s): Map<String, Int> =
                    List.fold((acc, p) -> %2$s, Map.empty, %3$s)

                behavior over : (src: %1$s, limit: Int) -> Map<String, Int>

                let over (src, limit) = Map.filterEntries((_, t) -> t >= limit, netOf(src))
                """;
        Compilation one = measured(model.formatted("List<Entry>", ADDING,
                "List.map(e -> e.inner, src)"));
        assertTrue(json(one).contains("total(src[*].inner.amount by account)"),
                () -> report(one));
        Compilation across = measured(model.formatted("List<List<Entry>>", ADDING,
                "List.map(e -> e.inner, List.flatMap(es -> es, src))"));
        assertTrue(json(across).contains("total(src[*][*].inner.amount by account)"),
                () -> report(across));
    }

    /**
     * An end of what a helper makes of each element is kept under its key as a total of it is:
     * the helper written twice in the step is one number of the element, which is what its two
     * calls are read as, and not two names.
     */
    @Test
    void anEndOfWhatAHelperMakesOfEachElementIsKeptUnderItsKey() {
        String model = signedOverTheLists(Int.ANY, "").replace("on -> on + signed(p)",
                "on -> Int.min(on, signed(p))");
        Compilation compilation = measured(model);
        assertTrue(report(compilation).contains("about `least({when side@Debit then 1·amount"),
                () -> report(compilation));
    }

    /**
     * An element that is its own key is a key as much as a field of it is: the total of the
     * elements equal to each is the line, spelled by the element itself, and the rows offered for
     * it meet it.
     */
    @Test
    void anElementThatIsItsOwnKeyIsTotalledUnderItself() {
        String model = """
                module example.ledger

                let totals (xs: List<Int>): Map<Int, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, x, n -> n + x, acc),
                              Map.empty, xs)

                behavior over : (xs: List<Int>, limit: Int) -> List<Int>

                let over (xs, limit) =
                    List.sort(Map.keys(Map.filterEntries((_, t) -> t >= limit, totals(xs))))
                %s""";
        Compilation before = measured(model.formatted(""));
        assertTrue(json(before).contains("total(xs[*] by itself)"), () -> report(before));
        Pattern row = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");
        StringBuilder written = new StringBuilder("\nexample over\n");
        int named = 0;
        for (String each : Adequacy.offeredFor(before.db(),
                        OfferingRequest.overTheModule("example.ledger"))
                .rowsByBehavior().getOrDefault("over", List.of()).stream()
                .map(offered -> String.join(", ",
                        offered.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList()) {
            Matcher matched = row.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            int limit = Integer.parseInt(matched.group(2));
            Map<Integer, Integer> totals = new LinkedHashMap<>();
            for (String x : matched.group(1).isEmpty() ? new String[0]
                    : matched.group(1).split(", ")) {
                totals.merge(Integer.parseInt(x), Integer.parseInt(x), Integer::sum);
            }
            List<Integer> kept = totals.entrySet().stream()
                    .filter(entry -> entry.getValue() >= limit).map(Map.Entry::getKey)
                    .sorted().toList();
            written.append("    | \"offered ").append(named++).append("\" : (").append(each)
                    .append(") -> ").append(kept).append("\n");
        }
        assertTrue(named > 0, () -> "rows are offered: " + report(before));
        Compilation after = measured(model.formatted(written));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * A total of nought is written as elements of the key coming to nought, and not as no element:
     * none files no key, so the comparison of what a key comes to is never made.
     */
    @Test
    void aTotalOfNoughtIsWrittenAsElementsComingToItAndNotAsNone() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Entry = { postings: List<Posting> }

                let netOf (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, List.flatMap(e -> e.postings, entries))

                behavior moved : (entries: List<Entry>) -> Map<String, Int>

                let moved (entries) =
                    Map.filterEntries((_, net) -> net /= 0, netOf(entries))
                %s""";
        Compilation before = measured(model.formatted(ADDING, ""));
        List<String> offered = Adequacy.offeredFor(before.db(),
                        OfferingRequest.overTheModule("example.ledger"))
                .rowsByBehavior().getOrDefault("moved", List.of()).stream()
                .map(row -> row.inputs().getFirst().text()).toList();
        assertTrue(offered.stream().anyMatch(row -> listsIn(row).stream()
                        .anyMatch(list -> !list.isEmpty())
                        && new Row(listsIn(row), 0).filed(Integer::sum).containsValue(0)),
                () -> "a row whose key comes to nought: " + offered);
        StringBuilder written = new StringBuilder("\nexample moved\n");
        int named = 0;
        for (String row : offered) {
            Map<String, Integer> kept = new LinkedHashMap<>();
            new Row(listsIn(row), 0).filed(Integer::sum).forEach((account, net) -> {
                        if (net != 0) {
                            kept.put(account, net);
                        }
                    });
            written.append("    | \"offered ").append(named++).append("\" : (").append(row)
                    .append(") -> ").append(entries(kept)).append("\n");
        }
        Compilation after = measured(model.formatted(ADDING, written));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * Two elements of one key holding four and ten, against fourteen: their total is on the line,
     * though neither of them is. Against ten, the total is past it, though one of them stands on
     * it.
     */
    @Test
    void theTotalOfAKeyAndNotAValueOfItIsWhatTheLineIsOn() {
        String two = List.of(new Posting("a", 4), new Posting("a", 10)).stream()
                .map(Posting::written).toList().toString();
        List<String> atFourteen = unmetOf(measured(overOneList(ADDING, """

                example over
                    | "four and ten" : (%s, 14) -> [("a", 14)]
                """.formatted(two))));
        assertFalse(atFourteen.contains("ON"), () -> "fourteen is on the line: " + atFourteen);
        List<String> atTen = unmetOf(measured(overOneList(ADDING, """

                example over
                    | "four and ten" : (%s, 10) -> [("a", 14)]
                """.formatted(two))));
        assertTrue(atTen.contains("ON"), () -> "fourteen is not on a line at ten: " + atTen);
    }

    /** Elements of another key are no part of this one's total, and two of one key in two lists
     *  of the outer list are. */
    @Test
    void theElementsOfAKeyAreGatheredFromEveryListAndNoOtherKeys() {
        List<String> unmet = unmetOf(measured(overTheLists(ADDING, """

                example over
                    | "apart" : ([Entry { postings = [%s, %s] }, Entry { postings = [%s] }], 14)
                        -> [("a", 14), ("b", 20)]
                """.formatted(new Posting("a", 4).written(), new Posting("b", 20).written(),
                new Posting("a", 10).written()))));
        assertFalse(unmet.contains("ON"), () -> "a's total is fourteen, on the line: " + unmet);
        assertFalse(unmet.contains("IN"), () -> "b's is twenty, past it: " + unmet);
    }

    /** The total written with its two values the other way round, as the library's addition, under
     *  a name given what the step answers, or as a lookup and a filing, is the same total. */
    @Test
    void theSameTotalWrittenAnotherWayIsTheSameLine() {
        List<String> plain = axisOf(measured(overOneList(ADDING, "")));
        assertFalse(plain.isEmpty(), "a line is drawn");
        for (String step : List.of(
                "Map.updateOrInsert(p.account, p.amount, on -> p.amount + on, acc)",
                "Map.updateOrInsert(p.account, p.amount, on -> Int.add(on, p.amount), acc)",
                "{ let next = " + ADDING + "  next }",
                "Map.updateOrInsert(p.account, p.amount,"
                        + " on -> { let a = p.amount  on + a }, acc)",
                """
                match Map.get(p.account, acc) with
                        | None -> Map.insert(p.account, p.amount, acc)
                        | Some on -> Map.insert(p.account, on + p.amount, acc)""")) {
            Compilation compilation = measured(overOneList(step, ""));
            assertEquals(plain, axisOf(compilation), () -> step + ": " + report(compilation));
        }
    }

    /**
     * What a fold files that is no total of one number of each element says nothing of one: the
     * first element files another number than the rest add, a further one adds something read of
     * what came before, or a list made of something new of each element.
     */
    @Test
    void aFoldThatAddsNoOneNumberOfEachElementIsNotReadAsATotal() {
        record Model(String step, String walked) { }
        String withAFee = """
                module example.ledger

                data Posting = { account: String, amount: Int, fee: Int }

                let netOf (postings: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, %s)

                behavior over : (postings: List<Posting>, limit: Int) -> Map<String, Int>

                let over (postings, limit) =
                    Map.filterEntries((_, net) -> net >= limit, netOf(postings))
                """;
        for (Model each : List.of(
                new Model("Map.updateOrInsert(p.account, p.amount, on -> on + p.fee, acc)",
                        "postings"),
                new Model("Map.updateOrInsert(p.account, p.amount, on -> on + on, acc)",
                        "postings"),
                new Model("Map.updateOrInsert(p.account, p.amount,"
                        + " on -> on + Map.size(acc), acc)", "postings"),
                new Model(ADDING, "List.map(q -> Posting { account = q.account,"
                        + " amount = q.amount * 2, fee = q.fee }, postings)"),
                new Model(ADDING, "List.map(q -> Posting { account = q.account,"
                        + " amount = q.fee, fee = q.amount }, postings)"))) {
            Compilation compilation = measured(withAFee.formatted(each.step(), each.walked()));
            assertFalse(json(compilation).contains("total(postings[*].amount"),
                    () -> each + ": " + report(compilation));
            assertTrue(report(compilation).contains("not read"),
                    () -> each + ": " + report(compilation));
        }
    }

    /**
     * What a helper makes of each element by its case is a number of the element and not a place
     * of it: the total of it under a key is a number of its own, read through the helper written
     * twice in the step.
     */
    @Test
    void aNumberAHelperMakesOfEachElementIsTotalledByItsKey() {
        Compilation compilation = measured(signedOverTheLists(Int.ANY, """

                example over
                    | "a debit and a credit" : ([Entry { postings = [
                          Posting { account = "a", side = Debit, amount = 10 },
                          Posting { account = "a", side = Credit, amount = 4 }] }], 6)
                        -> [("a", 6)]
                """));
        assertTrue(json(compilation).contains("\"gathered_under_its_key\""),
                () -> report(compilation));
        assertTrue(report(compilation).contains("total({"), () -> report(compilation));
        assertFalse(unmetOf(compilation).contains("ON"),
                () -> "ten less four is six, on the line: " + report(compilation));
    }

    /** The line is written in a document the schema shipped beside this accepts. */
    @Test
    void theDocumentNamingTheTotalIsOneTheSchemaAccepts() {
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                overOneList(ADDING, "")))));
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                overTheLists(ADDING, "")))));
    }

    private static String writtenAs(Row row, boolean acrossTheLists, Int limit) {
        List<String> lists = new ArrayList<>();
        for (List<Posting> list : row.lists()) {
            String postings = list.stream().map(Posting::written).toList().toString();
            lists.add(acrossTheLists ? "Entry { postings = " + postings + " }" : postings);
        }
        String written = acrossTheLists ? lists.toString() : lists.getFirst();
        return written + ", " + limit.written(row.limit());
    }

    private static String entries(Map<String, Integer> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    private static final Pattern ROW = Pattern.compile("^(.*), (?:Floor\\()?(-?\\d+)\\)?$");

    private static final Pattern POSTING = Pattern.compile(
            "Posting \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\"(?:, side = (Debit|Credit))?,"
                    + " amount = (-?\\d+) \\}");

    private static final Pattern ENTRY = Pattern.compile("Entry \\{ postings = \\[(.*?)\\] \\}");

    /** Every row the block offers, read back from how it is written; a row this cannot read back
     *  whole fails, since a part left unread is one nothing checks. */
    private static List<Row> offeredRows(Compilation compilation, boolean acrossTheLists) {
        List<Row> out = new ArrayList<>();
        for (String each : offeredInputs(compilation)) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            String written = matched.group(1);
            List<List<Posting>> lists = acrossTheLists ? listsIn(written)
                    : List.of(postingsIn(written.substring(1, written.length() - 1)));
            out.add(new Row(lists, Integer.parseInt(matched.group(2))));
        }
        return out;
    }

    /** The postings of each entry {@code entries} writes, in order. */
    private static List<List<Posting>> listsIn(String entries) {
        List<List<Posting>> lists = new ArrayList<>();
        Matcher entry = ENTRY.matcher(entries);
        while (entry.find()) {
            lists.add(postingsIn(entry.group(1)));
        }
        if (lists.isEmpty() && !entries.equals("[]")) {
            fail("the entries of an offered row are read back: " + entries);
        }
        return lists;
    }

    /** The postings {@code list} writes, read to its end. */
    private static List<Posting> postingsIn(String list) {
        List<Posting> postings = new ArrayList<>();
        Matcher one = POSTING.matcher(list);
        StringBuilder rest = new StringBuilder();
        while (one.find()) {
            postings.add(new Posting(one.group(1), one.group(2),
                    Integer.parseInt(one.group(3))));
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
                .rowsByBehavior().getOrDefault("over", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** The points of the lines drawn that no row is at, by name: {@code ON}, {@code OFF},
     *  {@code IN} and {@code OUT}. */
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

    /** The quantity each border is on, as the report names it. */
    private static List<String> axisOf(Compilation compilation) {
        List<JsonNode> borders = new ArrayList<>();
        collect(JSON.readTree(json(compilation)), borders);
        return borders.stream()
                .map(each -> each.path("axis").asString() + " " + each.path("value").asString())
                .toList();
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The source measured, which is a source that compiles. */
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
