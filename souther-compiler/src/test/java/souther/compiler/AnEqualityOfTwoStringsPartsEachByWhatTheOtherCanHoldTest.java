package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An equality between the strings at two positions parts each by what the other can hold.
 *
 * <p>The equality is true at a string only if the other position can hold it, so the strings the
 * other cannot hold are a class of this position the rule tells from the rest, whatever is written
 * at the other. Nothing is said where the two are tied, where a way narrows either before the
 * equality, or where what the other can hold is not worked out exactly: a class that would be
 * counted there is one a row can be owed at that no row can be written for.
 */
class AnEqualityOfTwoStringsPartsEachByWhatTheOtherCanHoldTest {

    private static final String LETTERS = "[a-z]+";

    private static final String LETTERS_AND_DIGITS = "[a-z0-9]+";

    /** The classes of each position the model divides, by the path of the position. */
    private static Map<String, List<String>> classesOf(String first, String second,
                                                       String body) {
        Compilation compilation = Compilation.ofSource("""
                module example.equal

                data L = String
                    invariant String.matches("%s", value)

                data M = String
                    invariant String.matches("%s", value)

                behavior f : (a: L, b: M) -> Bool

                let f (a, b) = %s
                """.formatted(first, second, body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Map<String, List<String>> out = new TreeMap<>();
        all.get("f").axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The classes of {@code a} and {@code b} of {@code f} over the two and a number {@code n}. */
    private static Map<String, List<String>> classesOfTheStringsBehind(String guard) {
        Compilation compilation = Compilation.ofSource("""
                module example.equal

                data L = String
                    invariant String.matches("%s", value)

                data M = String
                    invariant String.matches("%s", value)

                behavior f : (a: L, b: M, n: Int) -> Bool

                let f (a, b, n) = {
                    %s
                    a.value == b.value
                }
                """.formatted(LETTERS, LETTERS_AND_DIGITS, guard), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Map<String, List<String>> out = new TreeMap<>();
        all.get("f").axes().stream()
                .filter(axis -> axis.path().equals("a") || axis.path().equals("b"))
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The places of {@code f} whose equality is not shown to reach every value of them. */
    private static List<String> notShownToReachEveryValue(String lets) {
        Compilation compilation = Compilation.ofSource("""
                module example.equal

                data L = String
                    invariant String.matches("%s", value)

                data Row = { id: String, tag: String? }

                let tagIs (text: String, r: Row): Bool =
                    match r.tag with
                        | Some own -> own == text
                        | None -> false

                behavior f : (a: L, rows: List<Row>) -> List<Row>

                %s
                """.formatted(LETTERS, lets), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("f");
        assertNotNull(evidence, "the model under test compiles");
        return evidence.notRead().stream()
                .filter(each -> each.reason().name()
                        .equals("RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE"))
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /** A tag of a row, read in a filter beside a string, is parted by what that string can be. */
    @Test
    void theStringsOfAListsElementsAreParted() {
        assertEquals(List.of(), notShownToReachEveryValue(
                "let f (a, rows) = List.filter(r -> tagIs(a.value, r), rows)"));
    }

    /** The same, where the string reaches the filter as the one element of a list it is applied to. */
    @Test
    void theSameFilterAppliedFromAListOfTheStringIsParted() {
        assertEquals(List.of(), notShownToReachEveryValue(
                "let f (a, rows) = List.flatMap(t -> List.filter(r -> tagIs(t, r), rows),"
                        + " [ a.value ])"));
    }

    /** The classes of {@code f}'s positions, over an email and a book of rows with a domain. */
    private static Map<String, List<String>> classesOfAnEmailAgainstTheDomainsOfARow(
            String lets) {
        return classesAtOf("email", "[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+",
                "[a-z0-9]+(\\\\.[a-z0-9]+)+", lets);
    }

    /**
     * The classes at {@code path}, the emails and the domains being those {@code emails} and
     * {@code domains} spell.
     */
    private static Map<String, List<String>> classesAtOf(String path, String emails,
                                                         String domains, String lets) {
        Compilation compilation = Compilation.ofSource("""
                module example.pieces

                data Email = String
                    invariant String.matches("%s", value)

                data Domain = String
                    invariant String.matches("%s", value)

                data Row = { id: String, domain: Domain? }

                data Book = List<Row>

                let hasDomain (text: String, r: Row): Bool =
                    match r.domain with
                        | Some own -> own.value == text
                        | None -> false

                behavior f : (email: Email, book: Book) -> List<Row>

                %s
                """.formatted(emails, domains, lets), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Map<String, List<String>> out = new TreeMap<>();
        all.get("f").axes().stream().filter(axis -> axis.path().equals(path))
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    private static final Map<String, List<String>> THE_EMAILS_WHOSE_SECOND_PIECE_CAN_BE_A_DOMAIN =
            Map.of("email", List.of("email/x can be book[*].domain@Some",
                    "email/x is never book[*].domain@Some"));

    /**
     * The piece a lookup at an index written down picks of the pieces of a string is one value,
     * and the string it is of is parted by whether that piece can be what the other side holds.
     */
    @Test
    void theStringsWhoseSecondPieceCanBeTheOtherSideAreAClassOfTheString() {
        assertEquals(THE_EMAILS_WHOSE_SECOND_PIECE_CAN_BE_A_DOMAIN,
                classesOfAnEmailAgainstTheDomainsOfARow("""
                        let f (email, book) =
                            match List.get(1, String.split("@", email.value)) with
                                | Some d -> List.filter(r -> hasDomain(d, r), book.value)
                                | None -> []
                        """));
    }

    private static final String THE_SECOND_PIECE_OF_AN_EMAIL_AGAINST_A_BOOK = """
            let f (email, book) =
                match List.get(1, String.split("@", email.value)) with
                    | Some d -> List.filter(r -> hasDomain(d, r), book.value)
                    | None -> []
            """;

    /**
     * The other side is parted too where it is short: a domain of a row is a class of its own by
     * whether it is the second piece of some email, which only two domains are. A domain the
     * model bounds is a piece of a value whatever it is.
     */
    @Test
    void theDomainsThatAreTheSecondPieceOfSomeEmailAreAClassOfTheOtherSide() {
        assertEquals(Map.of("book[*].domain@Some", List.of(
                        "book[*].domain@Some/x can be piece 1 of email",
                        "book[*].domain@Some/x is never piece 1 of email")),
                classesAtOf("book[*].domain@Some", "[a-z]+@(a|b)\\\\.example",
                        "[a-z0-9]{1,63}(\\\\.[a-z0-9]{1,63}){1,3}",
                        THE_SECOND_PIECE_OF_AN_EMAIL_AGAINST_A_BOOK));
    }

    /**
     * A language holds sequences of code points, and a String holds only those in Normalization
     * Form C. The second piece of the one email the language reads as {@code e}, a combining acute
     * and {@code @b} is {@code b}, and no value has it: an email arrives as {@code é@b}, which the
     * language does not hold. So no domain is the second piece of an email but {@code a}, and
     * neither of the two domains the book can hold is parted by it.
     */
    @Test
    void aPieceOfAStringNoValueIsIsNoPieceOfAValue() {
        assertEquals(Map.of(), classesAtOf("book[*].domain@Some", "a@a|e\\\\u0301@b",
                "b|c", THE_SECOND_PIECE_OF_AN_EMAIL_AGAINST_A_BOOK));
    }

    /** And the emails are not parted by a piece only a string no value is has. */
    @Test
    void anEmailWhoseOnlyMatchingPieceIsThatOfAStringNoValueIsIsNotPartedByIt() {
        assertEquals(Map.of(), classesAtOf("email", "a@a|e\\\\u0301@b", "b|c",
                THE_SECOND_PIECE_OF_AN_EMAIL_AGAINST_A_BOOK));
    }

    /**
     * Where the domains have no length the model bounds, one near the longest string is the piece
     * of no email, though the language of the pieces holds it: the domains are not parted by it.
     */
    @Test
    void aDomainWithNoBoundOnItsLengthIsNotPartedByTheEmailsThatHoldIt() {
        assertEquals(Map.of(), classesAtOf("book[*].domain@Some", "[a-z]+@(a|b)\\\\.example",
                "[a-z0-9]+(\\\\.[a-z0-9]+)+", THE_SECOND_PIECE_OF_AN_EMAIL_AGAINST_A_BOOK));
    }

    /** And where the piece reaches the comparison through a list a function answers. */
    @Test
    void thePieceMayReachTheComparisonThroughAnAnsweredList() {
        assertEquals(THE_EMAILS_WHOSE_SECOND_PIECE_CAN_BE_A_DOMAIN,
                classesOfAnEmailAgainstTheDomainsOfARow("""
                        let domainsOf (email: Email): List<String> =
                            match List.get(1, String.split("@", email.value)) with
                                | Some d -> [ d ]
                                | None -> []

                        let f (email, book) =
                            List.flatMap(d -> List.filter(r -> hasDomain(d, r), book.value),
                                    domainsOf(email))
                        """));
    }

    /** And where the piece is attempted as a name, which is the string it is made of. */
    @Test
    void aPieceAttemptedAsANameIsTheSamePiece() {
        assertEquals(THE_EMAILS_WHOSE_SECOND_PIECE_CAN_BE_A_DOMAIN,
                classesOfAnEmailAgainstTheDomainsOfARow("""
                        let hasName (name: Domain, r: Row): Bool =
                            match r.domain with
                                | Some own -> own == name
                                | None -> false

                        let domainsOf (email: Email): List<Domain> =
                            match List.get(1, String.split("@", email.value)) with
                                | Some d -> if Domain(d) as name then [ name ] else []
                                | None -> []

                        let f (email, book) =
                            List.flatMap(d -> List.filter(r -> hasName(d, r), book.value),
                                    domainsOf(email))
                        """));
    }

    /** A guard on the string itself narrows it before the lookup, and nothing is said. */
    @Test
    void aGuardOnTheWholeStringPartsNothing() {
        assertEquals(Map.of(), classesOfAnEmailAgainstTheDomainsOfARow("""
                let f (email, book) = {
                    guard String.length(email.value) >= 8 else []
                    match List.get(1, String.split("@", email.value)) with
                        | Some d -> List.filter(r -> hasDomain(d, r), book.value)
                        | None -> []
                }
                """));
    }

    /** A guard on a number beside the two says nothing of their strings. */
    @Test
    void aGuardOnAnotherPositionLeavesTheStringsPartedAsTheyWere() {
        assertEquals(Map.of("b", List.of("b/x can be a", "b/x is never a")),
                classesOfTheStringsBehind("guard n >= 1 else false"));
    }

    /** A guard on the string itself narrows it before the equality, and nothing is said. */
    @Test
    void aGuardOnTheStringItselfPartsNothing() {
        assertEquals(Map.of(),
                classesOfTheStringsBehind("guard String.length(b.value) >= 2 else false"));
    }

    /** The strings of {@code b} that {@code a} cannot hold are a class of {@code b}'s own. */
    @Test
    void theStringsThePartnerCannotHoldAreAClassOfTheOther() {
        assertEquals(Map.of("b", List.of("b/x can be a", "b/x is never a")),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"));
    }

    /** It is the wider side that is parted: the narrower one's strings are all the other's. */
    @Test
    void itIsTheWiderSideThatIsParted() {
        assertEquals(Map.of("a", List.of("a/x can be b", "a/x is never b")),
                classesOf(LETTERS_AND_DIGITS, LETTERS, "a.value == b.value"));
    }

    @Test
    void twoLanguagesThatOverlapPartEachOther() {
        assertEquals(Map.of("a", List.of("a/x can be b", "a/x is never b"),
                        "b", List.of("b/x can be a", "b/x is never a")),
                classesOf("[a-c]+", "[b-d]+", "a.value == b.value"));
    }

    @Test
    void oneLanguageOnBothSidesPartsNeither() {
        assertEquals(Map.of(), classesOf(LETTERS, LETTERS, "a.value == b.value"));
    }

    /** The order of the two operands is not what parts them. */
    @Test
    void theOperandsOfTheEqualityMayBeWrittenEitherWayRound() {
        assertEquals(classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "b.value == a.value"));
    }

    /** A rule that the strings are unequal is about the same strings. */
    @Test
    void anInequalityPartsTheSamePositionsTheSameWay() {
        assertEquals(classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value == b.value"),
                classesOf(LETTERS, LETTERS_AND_DIGITS, "a.value /= b.value"));
    }

    /** A position set against itself is tied to itself, and what it can hold parts nothing. */
    @Test
    void aPositionSetAgainstItselfPartsNothing() {
        assertEquals(Map.of(), classesOf(LETTERS, LETTERS_AND_DIGITS, "b.value == b.value"));
    }
}
