package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.Carrier;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.BinaryOperator;
import java.util.function.UnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.IntStream;

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

    private static final String GREATEST =
            "Map.updateOrInsert(p.account, p.amount, n -> Int.max(n, p.amount), acc)";

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

    /** One row offered for {@code large}: the postings of each list, in order, and the key. */
    private record Row(List<List<Posting>> lists, String account) {

        /** What the lookup finds, or null where no element has the key. */
        Integer found(BinaryOperator<Integer> gathered) {
            Integer found = null;
            for (List<Posting> list : lists) {
                for (Posting each : list) {
                    if (each.account().equals(account)) {
                        found = found == null ? each.signed() : gathered.apply(found, each.signed());
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

    /**
     * A key that is what each element adds, and so the number: the elements of a key come to the
     * key as often as it occurs, so the key is chosen with the number and not before it. A row
     * at four holds the key at four, or at two with two of them, whichever the composer writes.
     */
    @Test
    void aKeyThatIsWhatEachElementAddsIsChosenWithTheNumber() {
        record Gathering(String step, BinaryOperator<Integer> gathered) {}
        for (Gathering way : List.of(
                new Gathering("n -> n + x", Integer::sum),
                new Gathering("n -> Int.min(n, x)", Math::min),
                new Gathering("n -> Int.max(n, x)", Math::max))) {
            String step = way.step();
            BinaryOperator<Integer> gathered = way.gathered();
            String model = itsOwnKey(step, "");
            Compilation before = measured(model);
            assertTrue(json(before).contains("by itself) equal to key"), () -> report(before));
            List<List<Integer>> offered = new ArrayList<>();
            List<Integer> keys = new ArrayList<>();
            for (String each : offeredInputs(before)) {
                Matcher matched = Pattern.compile("^\\[(.*)\\], (-?\\d+)$").matcher(each);
                assertTrue(matched.matches(), () -> "an offered row is one this reads back: " + each);
                List<Integer> xs = new ArrayList<>();
                if (!matched.group(1).isBlank()) {
                    for (String one : matched.group(1).split(", ")) {
                        xs.add(Integer.parseInt(one));
                    }
                }
                offered.add(xs);
                keys.add(Integer.parseInt(matched.group(2)));
            }
            assertFalse(offered.isEmpty(), () -> step + ": rows are offered: " + report(before));
            for (int at : new int[] {3, 4}) {
                assertTrue(IntStream.range(0, offered.size()).anyMatch(row -> Integer.valueOf(at)
                        .equals(foundIn(offered.get(row), keys.get(row), gathered))),
                        () -> step + ": a row finds " + at + ": " + offered + " " + keys);
            }
            StringBuilder examples = new StringBuilder("\nexample large\n");
            for (int row = 0; row < offered.size(); row++) {
                Integer found = foundIn(offered.get(row), keys.get(row), gathered);
                examples.append("    | \"offered ").append(row).append("\" : (")
                        .append(offered.get(row)).append(", ").append(keys.get(row)).append(") -> ")
                        .append(found != null && found >= 4).append("\n");
            }
            Compilation after = measured(itsOwnKey(step, examples.toString()));
            assertEquals(List.of(), unmetOf(after),
                    () -> step + ": the rows that were offered meet the line: " + report(after));
        }
    }

    private static Integer foundIn(List<Integer> xs, int key, BinaryOperator<Integer> gathered) {
        Integer found = null;
        for (int each : xs) {
            if (each == key) {
                found = found == null ? each : gathered.apply(found, each);
            }
        }
        return found;
    }

    private static String itsOwnKey(String step, String more) {
        return """
                module example.ledger

                let totals (xs: List<Int>): Map<Int, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, x, %s, acc), Map.empty, xs)

                behavior large : (xs: List<Int>, key: Int) -> Bool

                let large (xs, key) =
                    match Map.get(key, totals(xs)) with
                        | Some n -> n >= 4
                        | None -> false
                %s""".formatted(step, more);
    }

    /**
     * What a key's elements come to is read where the run answers, and whether it answers is the
     * run's: a row whose run stops at a sum on the way past the last number an {@code Int} holds,
     * in the order the walk hands the elements, stands at no point though what its elements come
     * to is the number the point is at. The same elements walked the other way round answer, and
     * stand there. A key asked for reads the elements as the key of an element does.
     */
    @Test
    void aRowWhoseRunStopsStandsAtNoPointWhateverItsElementsComeTo() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, p.amount,
                                              n -> n + p.amount, acc), Map.empty, %s)

                behavior large : (ps: List<Posting>, account: String) -> Bool

                let large (ps, account) =
                    match Map.get(account, totals(ps)) with
                        | Some amount -> amount >= 9223372036854775807
                        | None -> false

                example large
                    | "row" : (%s, "A") -> true
                """;
        String passing = List.of(posting(String.valueOf(Long.MAX_VALUE)), posting("1"),
                posting("-1")).toString();
        Compilation stops = ran(model.formatted("ps", passing));
        assertTrue(unmetOf(stops).contains("ON"),
                () -> "a row whose run stops is at no point: " + report(stops));
        Compilation reversed = ran(model.formatted("List.reverse(ps)", passing));
        assertFalse(unmetOf(reversed).contains("ON"),
                () -> "the same elements walked the other way round answer: " + report(reversed));
    }

    /**
     * What an example says a lookup answers is checked against what the program answers, so the
     * rows these tests write as examples are held to the answers computed for them: an example
     * that says nothing is found under a key whose elements come to a hundred is an example that
     * does not hold, and the compilation says so.
     */
    @Test
    void anExampleThatSaysWhatTheLookupDoesNotAnswerIsRefused() {
        String examples = """

                example large
                    | "wrong" : (%s, "A") -> false
                """.formatted(postings(new Posting("A", 60), new Posting("A", 40)));
        Compilation compilation = ran(overOneList(ADDING, examples));
        assertFalse(compilation.errors().isEmpty(),
                () -> "an example that does not hold is refused: " + report(compilation));
    }

    /**
     * What several keys come to is composed together because the elements of each key are the
     * elements of that key alone. Two totals of different fields of the same elements are not:
     * one element holds both, and nothing here chooses it for both. They are said to be not
     * composed together, and not to have no row.
     */
    @Test
    void severalTotalsOfDifferentFieldsOfOneContainerAreSaidNotToBeComposedTogether() {
        Compilation compilation = measured("""
                module example.ledger

                data Posting = { amount: Int, fee: Int }

                behavior both : (ps: List<Posting>) -> Bool

                let both (ps) =
                    List.sum(List.map(p -> p.amount, ps)) >= 100
                            && List.sum(List.map(p -> p.fee, ps)) >= 5
                """);
        assertTrue(report(compilation).contains("a condition on another number taken where this"
                + " row is already being written for one"), () -> report(compilation));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
    }

    private static String totalBesideACount(String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior few : (ps: List<Posting>, key: String) -> Bool

                let few (ps, key) =
                    match Map.get(key, totals(ps)) with
                        | Some n -> n >= 100
                                && List.length(List.filter(p -> p.account == key, ps)) <= 2
                        | None -> false
                %s""".formatted(ADDING, more);
    }

    /**
     * How many elements a key has is asked beside what they come to: a total of a hundred in at
     * most two elements is composed with one element or two, and a count the total has nothing to
     * say of is composed with the total.
     */
    @Test
    void aTotalBesideTheCountOfTheElementsOfItsKeyIsComposedTogether() {
        Compilation before = measured(totalBesideACount(""));
        Pattern row = Pattern.compile("^(.*), \"((?:[^\"\\\\]|\\\\.)*)\"$");
        StringBuilder examples = new StringBuilder("\nexample few\n");
        int named = 0;
        for (String each : offeredInputs(before, "few")) {
            Matcher matched = row.matcher(each);
            assertTrue(matched.matches(), () -> "an offered row is one this reads back: " + each);
            String written = matched.group(1);
            Row read = new Row(List.of(postingsIn(written.substring(1, written.length() - 1))),
                    matched.group(2));
            long counted = read.lists().getFirst().stream()
                    .filter(posting -> posting.account().equals(read.account())).count();
            Integer total = read.found(Integer::sum);
            examples.append("    | \"offered ").append(named++).append("\" : (").append(each)
                    .append(") -> ").append(total != null && total >= 100 && counted <= 2)
                    .append("\n");
        }
        assertTrue(named > 0, () -> "rows are offered: " + report(before));
        Compilation after = measured(totalBesideACount(examples.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the lines: " + report(after));
        assertFalse(report(after).contains("no row takes a decision rule"),
                () -> "every way through the lookup and the count is taken: " + report(after));
    }

    /**
     * A key filed in a map has an element, so a container asked how many it holds is asked the
     * counts of that from one, whether or not the set has nought in it: every size but three has
     * one and two in it, and has no key's.
     */
    @Test
    void aSetOfSizesWithNoughtInItIsAskedFromOneForAKeyFiledInAMap() {
        NumericSet butThree = new NumericSet.AwayFrom(List.of(Count.of(3)));
        ContainersAddingUp.HowManyIsAskedFor many =
                new ContainersAddingUp.HowManyIsAskedFor(butThree, Carrier.WHOLE, 1);
        assertFalse(many.holds(0), "none is no size of a key filed in a map");
        assertTrue(many.holds(1) && many.holds(2), "the sizes of the set from one stand");
        assertFalse(many.holds(3), "and the one it leaves out does not");
        assertTrue(new ContainersAddingUp.HowManyIsAskedFor(butThree, Carrier.WHOLE).holds(0),
                "a container asked nothing of it besides the set is asked its sizes as they are");
    }

    /**
     * The end of a key's values is written as one element, which is a way of writing it and not
     * what an end is: a key asked to have two elements is an end this does not write, and is said
     * to be one — not to be a count no key has.
     */
    @Test
    void anEndOfAKeyAskedToHaveMoreThanOneElementIsSaidNotToBeComposed() {
        Compilation compilation = measured("""
                module example.ledger

                data Posting = { account: String, amount: Int }

                let least (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior few : (ps: List<Posting>, key: String) -> Bool

                let few (ps, key) =
                    match Map.get(key, least(ps)) with
                        | Some n -> n >= 100
                                && List.length(List.filter(p -> p.account == key, ps)) == 2
                        | None -> false
                """.formatted(LEAST));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
    }

    /**
     * The end of a key's values is written as one element, which is a way of writing it and not
     * what an end is: a container its type makes hold two elements has none the end is one of,
     * and the end of the values of a key is still a number it comes to. It is said to be an end
     * this does not write, and not to be a number no row comes to — for the end of a key an input
     * holds and for the end of the key of an element alike.
     */
    @Test
    void anEndOfAContainerItsTypeMakesHoldTwoIsSaidNotToBeComposed() {
        String saidSome = "the ends of a key's values among more than one element of the key";
        Compilation asked = measured("""
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Pair = List<Posting>
                    invariant List.length(value) == 2

                let least (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior few : (ps: Pair, key: String) -> Bool

                let few (ps, key) =
                    match Map.get(key, least(ps.value)) with
                        | Some n -> n >= 100
                        | None -> false
                """.formatted(LEAST));
        assertTrue(report(asked).contains(saidSome), () -> report(asked));
        assertFalse(report(asked).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(asked));
        Compilation ofItsOwnKey = measured("""
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Pair = List<Posting>
                    invariant List.length(value) == 2

                data Entry = { postings: Pair }

                let least (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty,
                              List.flatMap(e -> e.postings.value, entries))

                behavior few : (entries: List<Entry>) -> Map<String, Int>

                let few (entries) =
                    Map.filterEntries((_, least) -> least >= 100, least(entries))
                """.formatted(LEAST));
        assertTrue(report(ofItsOwnKey).contains(saidSome), () -> report(ofItsOwnKey));
        assertFalse(report(ofItsOwnKey).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(ofItsOwnKey));
    }

    private static String twoKeys(String arm, String more) {
        return """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior both : (ps: List<Posting>, one: String, other: String) -> Bool

                let both (ps, one, other) =
                    match Map.get(one, totals(ps)) with
                        | Some a ->
                            match Map.get(other, totals(ps)) with
                                | Some b -> %s
                                | None -> false
                        | None -> false
                %s""".formatted(ADDING, arm, more);
    }

    /** What the arm of two lookups answers of what each found and of whether the keys are one. */
    private interface TwoKeysAnswer {

        boolean of(int one, int other, boolean sameKey);
    }

    /**
     * The rows offered for a lookup under two keys, written back as examples against what
     * {@code answer} says of them: every point of the lines drawn is met by them, and every way
     * through the two lookups is taken.
     */
    private static void assertTwoKeysAreComposedTogether(String arm, TwoKeysAnswer answer) {
        Compilation before = measured(twoKeys(arm, ""));
        Pattern row = Pattern.compile(
                "^(.*), \"((?:[^\"\\\\]|\\\\.)*)\", \"((?:[^\"\\\\]|\\\\.)*)\"$");
        StringBuilder examples = new StringBuilder("\nexample both\n");
        int named = 0;
        for (String each : offeredInputs(before, "both")) {
            Matcher matched = row.matcher(each);
            assertTrue(matched.matches(), () -> "an offered row is one this reads back: " + each);
            String postings = matched.group(1);
            Row read = new Row(List.of(postingsIn(postings.substring(1, postings.length() - 1))),
                    matched.group(2));
            Row other = new Row(read.lists(), matched.group(3));
            Integer one = read.found(Integer::sum);
            Integer two = other.found(Integer::sum);
            boolean holds = one != null && two != null
                    && answer.of(one, two, matched.group(2).equals(matched.group(3)));
            examples.append("    | \"offered ").append(named++).append("\" : (").append(each)
                    .append(") -> ").append(holds).append("\n");
        }
        assertTrue(named > 0, () -> "rows are offered: " + report(before));
        Compilation after = measured(twoKeys(arm, examples.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the lines: " + report(after));
        assertFalse(report(after).contains("no row takes a decision rule"),
                () -> "every way through the two lookups is taken: " + report(after));
    }

    /**
     * Two keys asked for of one fold are two totals of one container, and the container is
     * composed for both at once: the elements of each key are written holding it, the totals of
     * the two are what each line is drawn on, and a row at the point of one holds the other where
     * the way to it asks.
     */
    @Test
    void severalKeysAskedForOfOneFoldAreComposedTogether() {
        assertTwoKeysAreComposedTogether("a >= 100 && b < 50",
                (one, other, sameKey) -> one >= 100 && other < 50);
    }

    /**
     * Two parameters are not two keys: the same value held by both is one key, whose elements
     * come to one number for both. A lookup under each, held to be one key by the arm, is
     * composed with the keys at one value, as it is with them apart where the arm asks that.
     */
    @Test
    void twoParametersHoldingOneKeyAreOneKey() {
        assertTwoKeysAreComposedTogether("a >= 100 && b >= 100 && one == other",
                (one, other, sameKey) -> one >= 100 && other >= 100 && sameKey);
    }

    /**
     * One key asked two numbers that no elements come to together — a hundred or more and under
     * fifty, of one key — is a row no one writes. It is said to be a combination nothing
     * composed, and not to be one the model has no row at: the keys could stand apart.
     */
    @Test
    void twoNumbersAskedOfOneKeyThatNothingComesToAreSaidNotToBeComposed() {
        Compilation compilation = measured(twoKeys("a >= 100 && b < 50 && one == other", ""));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
    }

    /**
     * Keys are held apart where they can be, which is a way to try and not a rule: where the rules
     * leave two parameters one value, the lookups under them are of one key and the row is
     * composed with them at that value.
     */
    @Test
    void parametersTheRulesLeaveOneValueAreComposedAsOneKey() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Account = String
                    invariant value == "A"

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior both : (ps: List<Posting>, one: Account, other: Account) -> Bool

                let both (ps, one, other) =
                    match Map.get(one.value, totals(ps)) with
                        | Some a ->
                            match Map.get(other.value, totals(ps)) with
                                | Some b -> a >= 100 && b >= 100
                                | None -> false
                        | None -> false
                %s""".formatted(ADDING, "");
        Compilation compilation = measured(model);
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
        assertFalse(unmetOf(compilation).isEmpty(), () -> report(compilation));
        Pattern row = Pattern.compile("^(\\[.*\\]), Account\\(\"A\"\\), Account\\(\"A\"\\)$");
        StringBuilder examples = new StringBuilder("\nexample both\n");
        int named = 0;
        for (String each : offeredInputs(compilation, "both")) {
            Matcher matched = row.matcher(each);
            assertTrue(matched.matches(), () -> "an offered row is one this reads back: " + each);
            String postings = matched.group(1);
            Integer found = new Row(List.of(postingsIn(
                    postings.substring(1, postings.length() - 1))), "A").found(Integer::sum);
            examples.append("    | \"offered ").append(named++).append("\" : (").append(each)
                    .append(") -> ").append(found != null && found >= 100).append("\n");
        }
        assertTrue(named > 0, () -> "rows are offered: " + report(compilation));
        Compilation after = measured(model + examples);
        // The second lookup finds what the first does, so it is under a hundred only where the
        // first is, and the points below a hundred of the second are rows the first refuses: they
        // are the two left, and are not said to have no row.
        assertEquals(List.of("OFF", "OUT"), unmetOf(after),
                () -> "the rows that were offered meet the lines the keys at one value reach: "
                        + report(after));
        assertFalse(report(after).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(after));
    }

    private static String posting(String amount) {
        return "Posting { account = \"A\", amount = " + amount + " }";
    }

    /** The source measured, whose examples may stop where they run. */
    private static Compilation ran(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * The elements of a key in different lists of the outer list are one total: a hundred is sixty
     * in one list and forty in another, whatever other keys stand between them.
     */
    @Test
    void theElementsOfAKeyInDifferentListsAreOneTotal() {
        String examples = """

                example large
                    | "on" : ([Entry { postings = %1$s }, Entry { postings = %2$s }], "A") -> true
                    | "off" : ([Entry { postings = %1$s }, Entry { postings = %3$s }], "A") -> false
                """.formatted(
                postings(new Posting("A", 60), new Posting("B", 900)),
                postings(new Posting("B", 900), new Posting("A", 40)),
                postings(new Posting("A", 39)));
        List<String> unmet = unmetOf(measured(overTheLists(ADDING, examples)));
        assertFalse(unmet.contains("ON"), () -> "the point of a hundred is met: " + unmet);
        assertFalse(unmet.contains("OFF"), () -> "the point below it is met: " + unmet);
    }

    /**
     * Two lookups under one key are one number: what the second finds is what the first did, so a
     * row at ninety-nine for the second is a row at ninety-nine for the first as well, which the
     * first holds at a hundred or more to be asked at all. Read as two numbers, both would be
     * rows to write.
     */
    @Test
    void theSameKeyAskedForTwiceIsOneNumber() {
        String model = """
                module example.ledger

                data Posting = { account: String, amount: Int }

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> %s, Map.empty, ps)

                behavior large : (ps: List<Posting>, account: String) -> Bool

                let large (ps, account) =
                    match Map.get(account, totals(ps)) with
                        | Some a ->
                            match Map.get(%s, totals(ps)) with
                                | Some b -> a >= 100 && b >= 100
                                | None -> false
                        | None -> false
                """;
        Compilation twice = measured(model.formatted(ADDING, "account"));
        assertTrue(report(twice).contains("no row can stand at the OFF point (comparison@14:43)"),
                () -> report(twice));
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

    /** The end of a key's values is written as one element, which holds the key as the elements
     *  of a total do, so the keys held to a name are asked of the total alone. */
    @Test
    void aLineOnTheLeastOfAKeyAskedForIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(Keys.ANY, false, LEAST, Math::min);
        assertTheLineIsOfferedAndMet(Keys.ANY, true, LEAST, Math::min);
    }

    @Test
    void aLineOnTheGreatestOfAKeyAskedForIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(Keys.ANY, false, GREATEST, Math::max);
        assertTheLineIsOfferedAndMet(Keys.ANY, true, GREATEST, Math::max);
    }

    /**
     * What a helper makes of each element — a line's amount, taken off on the credit side — is
     * totalled under the key asked for as what the elements come to, in one list and across the
     * lists of an outer list alike, and the rows offered are of the case each arm takes.
     */
    @Test
    void aLineOnTheTotalOfWhatAHelperMakesOfEachElementIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(Keys.ANY, false,
                ATotalLookedUpUnderAKeyAskedForIsReadAsTheElementsOfThatKeyTest::signedOverOneList,
                Integer::sum);
        assertTheLineIsOfferedAndMet(Keys.ANY, true,
                ATotalLookedUpUnderAKeyAskedForIsReadAsTheElementsOfThatKeyTest::signedOverTheLists,
                Integer::sum);
    }

    private static String over(Keys keys, boolean acrossTheLists, String step, String more) {
        return acrossTheLists ? overTheLists(keys, step, more) : overOneList(keys, step, more);
    }

    private static final String SIGNED = """
            module example.ledger

            data Side = Debit | Credit

            data Posting = { account: String, side: Side, amount: Int }

            let signed (p: Posting): Int =
                match p.side with
                    | Debit -> p.amount
                    | Credit -> 0 - p.amount
            """;

    private static String signedOverOneList(String more) {
        return SIGNED + """

                let totals (ps: List<Posting>): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, signed(p),
                                              n -> n + signed(p), acc), Map.empty, ps)

                behavior large : (ps: List<Posting>, account: String) -> Bool

                let large (ps, account) =
                    match Map.get(account, totals(ps)) with
                        | Some amount -> amount >= 100
                        | None -> false
                """ + more;
    }

    private static String signedOverTheLists(String more) {
        return SIGNED + """

                data Entry = { postings: List<Posting> }

                let totals (entries: List<Entry>): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, signed(p),
                                              n -> n + signed(p), acc),
                              Map.empty, List.flatMap(e -> e.postings, entries))

                behavior large : (entries: List<Entry>, account: String) -> Bool

                let large (entries, account) =
                    match Map.get(account, totals(entries)) with
                        | Some amount -> amount >= 100
                        | None -> false
                """ + more;
    }

    private static void assertTheLineIsOfferedAndMet(Keys keys, boolean acrossTheLists,
                                                     String step,
                                                     BinaryOperator<Integer> gathered) {
        assertTheLineIsOfferedAndMet(keys, acrossTheLists,
                more -> over(keys, acrossTheLists, step, more), gathered);
    }

    private static void assertTheLineIsOfferedAndMet(Keys keys, boolean acrossTheLists,
                                                     UnaryOperator<String> modelWith,
                                                     BinaryOperator<Integer> gathered) {
        String examples = """

                example large
                    | "none" : ([], %s) -> false
                """.formatted(keys.written("AB"));
        String model = modelWith.apply(examples);
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
        Compilation after = measured(modelWith.apply(written.toString()));
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
            "Posting \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\"(?:, side = (Debit|Credit))?,"
                    + " amount = (-?\\d+) \\}");

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
            postings.add(new Posting(one.group(1), one.group(2), Integer.parseInt(one.group(3))));
            one.appendReplacement(rest, "");
        }
        one.appendTail(rest);
        if (!rest.toString().replace(",", "").isBlank()) {
            fail("the postings of an offered row are read to the end: " + list);
        }
        return postings;
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return offeredInputs(compilation, "large");
    }

    private static List<String> offeredInputs(Compilation compilation, String behavior) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.ledger"))
                .rowsByBehavior().getOrDefault(behavior, List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /**
     * The points of the lines drawn that no row is shown to be at, by name: those unmet, and
     * those undecided because no row was composed there, which is not the same report and is the
     * one a line nothing composes a row for comes back in.
     */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("point") && node.has("disposition")
                && !node.path("disposition").asString().equals("met")) {
            out.add(node.path("point").asString().toUpperCase(Locale.ROOT));
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

    /** The source measured, which is a source that compiles and whose examples hold: an example
     *  that says what the program does not answer is an error of the compilation
     *  ({@link #anExampleThatSaysWhatTheLookupDoesNotAnswerIsRefused}). */
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
