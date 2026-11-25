package souther.compiler.query;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A name on an import list names what its line brings in under it — the same thing a use of the
 * name in the body denotes, whichever kind of thing that is: a data, a helper, a library
 * operation. And an entry its line could not bring in names nothing, as a use of it would: a name
 * the module declares and does not expose is not reached by being written on a list.
 *
 * <p>What an editor stands on when it is asked about a list entry. Which entries are answered at
 * all is {@link EveryNameACompilingModelWritesIsAnsweredTest}'s; that the answer is the one the
 * body's uses get is this.
 */
class AnImportListEntryNamesWhatItsLineBringsInTest {

    private static final String LIB = """
            module lib exposing ( Amount, scaled )

            data Amount = { value: Int }

            let scaled (a: Amount, by: Int): Amount = Amount { value = a.value * by }

            let hidden (n: Int): Int = n
            """;

    private static final String MODEL = """
            module m exposing ( total )

            import lib ( Amount, scaled )

            import List ( sum )

            behavior total : (xs: List<Int>) -> Int

            let total (xs) = sum(xs)

            let bigger (a: Amount): Amount = scaled(a, 2)
            """;

    private static final String REACHING = """
            module n

            import lib ( hidden )
            """;

    private static final Map<String, String> TEXTS = texts();

    private static final Compilation COMPILATION =
            Compilation.ofDocuments(TEXTS, Set.of(), ModulePath.EMPTY);

    private static Map<String, String> texts() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("lib.sou", LIB);
        out.put("m.sou", MODEL);
        out.put("n.sou", REACHING);
        return out;
    }

    /**
     * What the compiler answers the name in brackets denotes, in either namespace, on the first
     * line of {@code file} that reads as {@code marked} does without them.
     */
    private static Object denotedAt(String file, String marked) {
        String plain = marked.replace("[", "").replace("]", "");
        int offset = TEXTS.get(file).indexOf(plain) + marked.indexOf('[');
        SourcePos at = COMPILATION.db().ask(new Front.LayoutOf(new SourceId(file))).value()
                .placeAt(offset);
        Object type = COMPILATION.db().ask(new Names.TypeAt(at)).value();
        return type != null ? type : COMPILATION.db().ask(new Names.ValueAt(at)).value();
    }

    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "import lib ( [Amount], scaled ) | let bigger (a: [Amount]): Amount",
            "import lib ( Amount, [scaled] ) | = [scaled](a, 2)",
            "import List ( [sum] )           | let total (xs) = [sum](xs)"})
    void anEntryNamesWhatTheBodyUsesItFor(String entry, String use) {
        Object used = denotedAt("m.sou", use);

        assertNotNull(used, use);
        assertEquals(used, denotedAt("m.sou", entry));
    }

    @Test
    void anEntryTheLineCannotBringInNamesNothing() {
        assertNull(denotedAt("n.sou", "import lib ( [hidden] )"));
    }
}
