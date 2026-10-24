package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReplacementDisposition;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A rewrite of what keeps some of the pieces of a string is told by a string whose pieces are all
 * ones the body goes on to build a newtype of.
 *
 * <p>The body parts a string, drops a piece, and attempts a construction of each piece left. A
 * rewrite that keeps the dropped piece changes the answer only where that piece is also one the
 * construction accepts; no class of the input holds that, since what the construction accepts is
 * stated of a value made from the string. The string is looked for as a language: what the input
 * admits, met with a sequence of pieces of the newtype the body attempts, so a string the input
 * admits only in one shape is found in that shape.
 */
class ARewriteOfWhatKeepsSomePiecesIsToldByPiecesMeetingWhatTheBodyDemandsTest {

    private static final String ADDRESS = """
            module example.crm

            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

            behavior domainOf : (email: EmailAddress) -> List<DomainName>
                constructs DomainName

            let domainOf (email) =
                List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            example domainOf
                | "a plain address" : (EmailAddress("cto@acme.example.com"))
                    -> [DomainName("acme.example.com")]
            """;

    /**
     * Another separator and another pattern than email's, over an input that is no email.
     *
     * @param inputInvariant the pattern the list is held to
     * @param row            the one example row
     */
    private static String tags(String inputInvariant, String row) {
        return """
                module example.catalog

                data TagList = String
                    invariant String.matches("%s", value)
                data Tag = String
                    invariant String.matches("[A-Z]{2}[0-9]", value)

                behavior tagsOf : (list: TagList) -> List<Tag>
                    constructs Tag

                let tagsOf (list) =
                    List.flatMap(t -> if Tag(t) as tag then [ tag ] else [],
                                 List.drop(1, String.split(";", list.value)))

                example tagsOf
                    | "the row" : %s
                """.formatted(inputInvariant, row);
    }

    private static Replacements.Searched searched(String model, String module, String behavior) {
        Collection<Replacements.Searched> all = searchedAll(model, module, behavior);
        assertEquals(1, all.size(), "the one rewrite the rows left open");
        return all.iterator().next();
    }

    private static Collection<Replacements.Searched> searchedAll(String model, String module,
                                                                 String behavior) {
        Compilation c = Compilation.ofSource(model, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        return c.db().ask(new Replacements.Witnesses(module, behavior)).value().values();
    }

    /** `cto@acme.example.com` keeps `cto` under the rewrite, which is no domain name. */
    @Test
    void aPartBeforeTheSeparatorThatIsADomainNameTellsTheRewriteApart() {
        Replacements.Searched came = searched(ADDRESS, "example.crm", "domainOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "`a.b@c.d` keeps `a.b`, which the construction accepts: " + came);
    }

    @Test
    void anotherSeparatorAndAnotherPatternAreReadFromTheBody() {
        Replacements.Searched came = searched(
                tags("[^;]+;[^;]+", "(TagList(\"x;AB1\")) -> [Tag(\"AB1\")]"),
                "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "`AA0;AB1` keeps `AA0`, which the construction accepts: " + came);
    }

    /**
     * The pieces are looked up in another input, as a lead's domain is looked up in the books. The
     * dropped piece changes the answer only where it is a domain the books hold, which no language
     * of the pieces states: the string is put together of what the row already holds.
     */
    private static final String LOOKED_UP = """
            module example.crm

            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

            behavior known : (email: EmailAddress, books: List<DomainName>) -> List<DomainName>
                constructs DomainName

            let domainsOf (email: EmailAddress): List<DomainName> =
                List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let known (email, books) =
                List.filter(d -> List.any(b -> b == d, books), domainsOf(email))

            example known
                | "a domain the books hold" :
                    (EmailAddress("cto@acme.example.com"), [DomainName("acme.example.com")])
                    -> [DomainName("acme.example.com")]
            """;

    @Test
    void aPieceTheRowHoldsElsewhereIsOneThePiecesAreMadeOf() {
        Replacements.Searched came = searched(LOOKED_UP, "example.crm", "known");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "`acme.example.com@acme.example.com` keeps a piece the books hold: " + came);
        assertEquals("EmailAddress(\"acme.example.com@acme.example.com\")",
                came.inputs().getFirst(),
                "the piece before the separator is the domain the books hold");
    }

    /**
     * A body that makes the string into something else before it parts it.
     *
     * @param conversion  the case conversion the body applies
     * @param source      the pattern the input is held to
     * @param piece       the pattern the newtype built of a piece is held to
     * @param row         the one example row
     */
    private static String converted(String conversion, String source, String piece, String row) {
        return """
                module example.catalog

                data Source = String
                    invariant String.matches("%s", value)
                data Part = String
                    invariant String.matches("%s", value)

                behavior partsOf : (source: Source) -> List<Part>
                    constructs Part

                let partsOf (source) =
                    List.flatMap(p -> if Part(p) as part then [ part ] else [],
                                 List.drop(1, String.split("@", String.%s(source.value))))

                example partsOf
                    | "the row" : %s
                """.formatted(source, piece, conversion, row);
    }

    /**
     * The input admits capitals only and the newtype small letters only, and the body makes the
     * input small before it parts it: the pieces the newtype is built of are the pieces of the small
     * string, so the string that tells the rewrite apart is capitals whose small form is a part.
     */
    @Test
    void aStringIsLookedForAmongThoseTheConversionMakesIntoPiecesTheNewtypeAdmits() {
        Replacements.Searched came = searched(
                converted("lowercase", "[A-Z]{1,2}@[A-Z]{2}", "[a-z]{2}",
                        "(Source(\"X@CD\")) -> [Part(\"cd\")]"),
                "example.catalog", "partsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "two capitals before the separator are two small letters once made small: "
                        + came);
        assertEquals(true, came.inputs().getFirst().matches("Source\\(\"[A-Z]{2}@CD\"\\)"),
                () -> "the piece before the separator is two capitals: " + came.inputs());
    }

    @Test
    void theConversionIsReadInTheOtherDirectionToo() {
        Replacements.Searched came = searched(
                converted("uppercase", "[a-z]{1,2}@[a-z]{2}", "[A-Z]{2}",
                        "(Source(\"x@cd\")) -> [Part(\"CD\")]"),
                "example.catalog", "partsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "two small letters are two capitals once made capitals: " + came);
        assertEquals(true, came.inputs().getFirst().matches("Source\\(\"[a-z]{2}@cd\"\\)"),
                () -> "the piece before the separator is two small letters: " + came.inputs());
    }

    /**
     * Where the conversion cannot be undone for the strings the input admits, nothing is offered:
     * the input admits only small letters, which a body that makes them small does not change, and
     * the newtype asks for capitals, which no small string becomes.
     */
    @Test
    void whereNoStringBecomesAPieceTheNewtypeAdmitsTheRewriteIsLeftUndecided() {
        Collection<Replacements.Searched> came = searchedAll(
                converted("lowercase", "[a-z]{1,2}@[a-z]{2}", "[A-Z]{2}",
                        "(Source(\"x@cd\")) -> []"),
                "example.catalog", "partsOf");

        assertEquals(List.of(), came.stream()
                .filter(each -> each.disposition() instanceof ReplacementDisposition.Witnessed)
                .toList(), "capitals are not what small letters are made into");
    }

    /**
     * A newtype held to two patterns is held to both in the place of each piece, so the string that
     * tells the rewrite apart is in the meet of the two.
     */
    @Test
    void aNewtypeHeldToTwoPatternsIsHeldToBothInThePlaceOfAPiece() {
        String model = """
                module example.catalog

                data TagList = String
                    invariant String.matches("[^;]+;[^;]+", value)
                data Tag = String
                    invariant String.matches("[A-Z]{2}[0-9]", value)
                    invariant String.matches("Z.*", value)

                behavior tagsOf : (list: TagList) -> List<Tag>
                    constructs Tag

                let tagsOf (list) =
                    List.flatMap(t -> if Tag(t) as tag then [ tag ] else [],
                                 List.drop(1, String.split(";", list.value)))

                example tagsOf
                    | "the row" : (TagList("x;ZB1")) -> [Tag("ZB1")]
                """;
        Replacements.Searched came = searched(model, "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "the piece before the separator is a tag that starts with `Z`: " + came);
        assertEquals(true, came.inputs().getFirst().matches("TagList\\(\"Z[A-Z][0-9];ZB1\"\\)"),
                () -> "both patterns hold of the piece: " + came.inputs());
    }

    /**
     * What a string is put together of and the strings the row offers it are counted apart: a string
     * of two pieces in a row of many strings is cut at the second and not at the first.
     */
    @Test
    void theStringsOfTheRowAreACountOfTheirOwn() {
        String books = String.join(", ", java.util.stream.IntStream.range(0, 9)
                .mapToObj(each -> "DomainName(\"d" + each + ".example.com\")").toList());
        String model = """
                module example.crm

                data EmailAddress = String
                    invariant String.matches("[a-z]+@[a-z0-9.]+\\\\.[a-z0-9]+", value)
                data DomainName = String
                    invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

                behavior known : (email: EmailAddress, books: List<DomainName>) -> List<DomainName>
                    constructs DomainName

                let domainsOf (email: EmailAddress): List<DomainName> =
                    List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                                 List.drop(1, String.split("@", String.lowercase(email.value))))

                let known (email, books) =
                    List.filter(d -> List.any(b -> b == d, books), domainsOf(email))

                example known
                    | "a domain the books hold" :
                        (EmailAddress("cto@d0.example.com"), [%s]) -> [DomainName("d0.example.com")]
                """.formatted(books);
        Collection<Replacements.Searched> came = searchedAll(model, "example.crm", "known");
        String said = came.stream().map(each -> each.disposition().toString()).toList().toString();

        assertEquals(true, said.contains("STRINGS_OF_THE_ROW_A_PIECE_IS_TAKEN_FROM"),
                () -> "the strings of the row were cut: " + said);
        assertEquals(false, said.contains("PIECES_A_STRING_IS_PUT_TOGETHER_OF"),
                () -> "the places of the string were not: " + said);
    }

    /**
     * The string stands inside one case of a sum, as an address does inside a contact point. The
     * body reaches it by the case it is, and the value a run had is that case: the two are the same
     * place.
     */
    private static final String IN_A_CASE = """
            module example.crm

            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data PhoneNumber = String
                invariant String.matches("[0-9]+", value)
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)
            data ByEmail = { email: EmailAddress }
            data ByPhone = { phone: PhoneNumber }
            data Reach = ByEmail | ByPhone

            behavior domainsOf : (reach: Reach) -> List<DomainName>
                constructs DomainName

            let emailsOf (reach: Reach): List<EmailAddress> =
                match reach with
                    | ByEmail { email = own } -> [ own ]
                    | ByPhone                 -> []

            let domainsOf (reach) =
                List.flatMap(e -> List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                                               List.drop(1, String.split("@", e.value))),
                             emailsOf(reach))

            example domainsOf
                | "an address" : (ByEmail { email = EmailAddress("cto@acme.example.com") })
                    -> [DomainName("acme.example.com")]
            """;

    @Test
    void aStringInsideOneCaseOfASumIsTheOneTheBodyParts() {
        Replacements.Searched came = searched(IN_A_CASE, "example.crm", "domainsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "the address inside `ByEmail` is the string parted: " + came);
    }

    /**
     * A string with no separator is one piece. Dropped, it leaves nothing; kept, it is the piece the
     * construction goes on with, so a string of that one piece tells the rewrite apart.
     */
    @Test
    void aStringThatHoldsNoSeparatorIsOnePieceAndIsLookedFor() {
        Replacements.Searched came = searched(
                tags("[^;]+(;[^;]+)?", "(TagList(\"xx\")) -> []"), "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "a lone `AA0` keeps a piece the construction accepts: " + came);
        assertEquals(List.of("TagList(\"AA0\")"), came.inputs(),
                "the string that is the one piece, with no separator in it");
    }

    /**
     * A string of very many pieces costs what one of a few does: the strings put together are of
     * as many pieces as the one seen, up to a bound, and are made as the search asks for them.
     */
    @Test
    void aStringOfManyPiecesIsNotMadeOutInFull() {
        String many = String.join(";", Collections.nCopies(12, "x"));
        Collection<Replacements.Searched> came = searchedAll(
                tags("[^;]+(;[^;]+)*", "(TagList(\"" + many + "\")) -> []"),
                "example.catalog", "tagsOf");

        assertEquals(List.of(), came.stream()
                .filter(each -> !(each.disposition() instanceof ReplacementDisposition.Witnessed))
                .toList(), "every rewrite the rows left open is told apart by a string put together");
    }

    /**
     * Where the strings are not made for want of a bound, the rewrite is left undecided and the
     * figure it stopped at is said, so that a reader knows which to raise.
     */
    @Test
    void aStringPastTheBoundSaysTheFigureItStoppedAt() {
        String many = "x" + String.join("", Collections.nCopies(11, ";AB1"));
        Replacements.Searched came = searched(
                tags("x(;[A-Z]{2}[0-9])*", "(TagList(\"" + many + "\")) -> [Tag(\"AB1\")]"),
                "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.NoneFound.class, came.disposition(),
                () -> "no string of the input has a first piece the construction accepts: " + came);
        assertEquals(true, came.disposition().toString()
                        .contains("PIECES_A_STRING_IS_PUT_TOGETHER_OF"),
                () -> "the bound the strings were cut at is said: " + came);
    }

    /**
     * The input admits only `ZZ9` before the separator, and the type alone would offer `AA0`: the
     * string that tells the rewrite apart is in the meet of the two, and only there.
     */
    @Test
    void whatTheInputAdmitsAndWhatTheNewtypeAdmitsAreMet() {
        Replacements.Searched came = searched(
                tags("(x|ZZ9);AB1", "(TagList(\"x;AB1\")) -> [Tag(\"AB1\")]"),
                "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came.disposition(),
                () -> "only `ZZ9;AB1` is a string of the input whose first piece is a tag: "
                        + came);
        assertEquals(List.of("TagList(\"ZZ9;AB1\")"), came.inputs());
    }

    /**
     * The control: where the input never lets the first piece be one the construction accepts, no
     * string meets both, and the rewrite is left undecided rather than said to be told apart.
     */
    @Test
    void whereTheInputRefusesEveryPieceTheBodyDemandsTheRewriteIsLeftUndecided() {
        Replacements.Searched came = searched(
                tags("[a-z]+;[A-Z]{2}[0-9]", "(TagList(\"x;AB1\")) -> [Tag(\"AB1\")]"),
                "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.NoneFound.class, came.disposition(),
                () -> "no input keeps a first piece the construction accepts: " + came);
    }
}
