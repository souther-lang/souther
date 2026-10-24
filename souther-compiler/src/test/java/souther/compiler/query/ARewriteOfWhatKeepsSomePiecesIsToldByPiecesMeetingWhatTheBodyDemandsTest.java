package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReplacementDisposition;

import java.util.Collection;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A rewrite of what keeps some of the pieces of a string is told by a string whose dropped piece is
 * one the body would have gone on with.
 *
 * <p>The body parts a string, drops a piece, and attempts a construction of each piece left. A
 * rewrite that keeps the dropped piece changes the answer only where that piece is also one the
 * construction accepts; no class of the input holds that, since what the construction accepts is
 * stated of a value made from the string and not of the string. The separator and the pattern are
 * read off the body, so what the search offers is not particular to one of them.
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

    /** Another separator, another pattern, and an input that is no email. */
    private static String tags(String inputInvariant) {
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
                    | "a list of two" : (TagList("x;AB1")) -> [Tag("AB1")]
                """.formatted(inputInvariant);
    }

    private static ReplacementDisposition searched(String model, String module,
                                                   String behavior) {
        Compilation c = Compilation.ofSource(model, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        Collection<Replacements.Searched> all = c.db()
                .ask(new Replacements.Witnesses(module, behavior)).value().values();
        assertEquals(1, all.size(), "the one rewrite the rows left open");
        return all.iterator().next().disposition();
    }

    /** `cto@acme.example.com` keeps `cto` under the rewrite, which is no domain name. */
    @Test
    void aPartBeforeTheSeparatorThatIsADomainNameTellsTheRewriteApart() {
        ReplacementDisposition came = searched(ADDRESS, "example.crm", "domainOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came,
                () -> "`a.b@c.d` keeps `a.b`, which the construction accepts: " + came);
    }

    @Test
    void anotherSeparatorAndAnotherPatternAreReadFromTheBody() {
        ReplacementDisposition came = searched(tags("[^;]+;[^;]+"), "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came,
                () -> "`AA0;AB1` keeps `AA0`, which the construction accepts: " + came);
    }

    /**
     * The control: where the input never lets the first piece be one the construction accepts, no
     * candidate meeting the demand is a value of the input, and the rewrite is left undecided
     * rather than said to be told apart.
     */
    @Test
    void whereTheInputRefusesEveryPieceTheBodyDemandsTheRewriteIsLeftUndecided() {
        ReplacementDisposition came =
                searched(tags("[a-z]+;[A-Z]{2}[0-9]"), "example.catalog", "tagsOf");

        assertInstanceOf(ReplacementDisposition.NoneFound.class, came,
                () -> "no input keeps a first piece the construction accepts: " + came);
    }
}
