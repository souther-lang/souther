package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The listing writes each name the way its caller writes it. A {@code let} with a parameter list is
 * a function and is called with one; a {@code let} without is a value, and applying one is refused
 * ({@code <<fn-declaration>>}, E1803). A value written in the listing with an argument list teaches
 * the single form the checker rejects, and the listing is where the documentation sends a reader to
 * find out how a name is called.
 *
 * <p>Which of the two a name is comes from the surface the listing is built from, not from a list of
 * names kept here: a parameter list is empty when the declaration had none, and the language admits
 * no second reading of that — an empty {@code ()} is refused. So a value the library publishes later
 * is held to this without the check being told about it.
 */
class AListedValueIsWrittenWithoutAnArgumentListTest {

    private static String listing() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = ApiCommand.run(new String[]{},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        assertEquals(0, code, err.toString(StandardCharsets.UTF_8));
        return out.toString(StandardCharsets.UTF_8);
    }

    /** What a line writes before the type it answers with: the name, and the argument list where one
     *  is written. The type is left out, since a parameter's own type has parentheses of its own. */
    private static String calledAs(String line) {
        int type = line.indexOf(" : ");
        return type < 0 ? line : line.substring(0, type);
    }

    @Test
    void anArgumentListIsWrittenExactlyWhereTheDeclarationDeclaresOne() {
        Map<String, ApiCommand.Signature> surface = ApiCommand.surface(souther.compiler.DefaultStdlib.get());
        List<String> values = new ArrayList<>();
        List<String> functions = new ArrayList<>();

        for (String line : listing().lines().toList()) {
            String called = calledAs(line);
            int open = called.indexOf('(');
            String name = open < 0 ? called : called.substring(0, open);
            ApiCommand.Signature signature = surface.get(name);
            assertNotNull(signature, "the listing writes a name the surface does not publish: " + line);
            if (signature.paramNames().isEmpty()) {
                values.add(name);
                assertEquals(name, called,
                        "`" + name + "` declares no parameter list, so it is a value and applying it"
                                + " is refused — the listing must not write it as a call: " + line);
            } else {
                functions.add(name);
                assertTrue(open >= 0,
                        "`" + name + "` declares parameters, so a caller writes an argument list: " + line);
            }
        }

        assertFalse(values.isEmpty(), "no value was checked at all — the scan settles nothing");
        assertFalse(functions.isEmpty(), "no function was checked at all — the scan settles nothing");
    }

    @Test
    void theEmptyCollectionsAreListedTheWayTheSpecificationSaysTheyAreWritten() {
        List<String> lines = listing().lines().toList();

        assertTrue(lines.contains("Map.empty : Map<'k, 'a>"), listing());
        assertTrue(lines.contains("Set.empty : Set<'a>"), listing());
        assertTrue(lines.stream().noneMatch(l -> l.contains("empty()")),
                "`Map.empty()` is the spelling the specification says is never written:\n" + listing());
    }

    /** Every form of the answer is the same rendering, so a reader asking for one name is told what
     *  the whole listing tells. */
    @Test
    void aNameLookedUpOnItsOwnIsWrittenTheSameWay() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = ApiCommand.run(new String[]{"Map.empty"},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));

        assertEquals(0, code, err.toString(StandardCharsets.UTF_8));
        assertEquals("Map.empty : Map<'k, 'a>", out.toString(StandardCharsets.UTF_8).strip());
    }
}
