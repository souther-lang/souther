package souther.compiler.doc;

import souther.compiler.DefaultStdlib;
import souther.compiler.Reserved;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeSet;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The published surface is written down twice: once as the library's own declarations, and once as
 * the block of names each module's specification section opens with. The second is what a reader
 * reads and what `souther doc` prints, and nothing held the two together — a rename could land on
 * the declarations, on the snapshot of them, and on the prose that explains the new name, and leave
 * the block naming a function that no longer exists.
 *
 * <p>What is checked is membership, not layout. The rows are the document's own grouping and the
 * prose points at them by position, so generating the block from the declarations would have to
 * invent that grouping or lose it. Which names are in the block is the part that can silently
 * disagree with the library, and it is the part fixed here; how they are spread over rows stays the
 * document's to decide.
 *
 * <p>The block is found by its shape rather than by a marker written beside it, and exactly one per
 * section is required. A second block of bare names is a failure that says so, rather than a union
 * that quietly admits whatever else was written in the section.
 */
class EveryOperationAModulePublishesIsListedInItsSectionTest {

    /** A row of the block: bare names separated by spaces, with nothing else on the line. */
    private static final Pattern NAME_ROW = Pattern.compile("[a-z][a-zA-Z0-9]*( +[a-z][a-zA-Z0-9]*)*");

    /** A listing delimiter: four or more dashes. The block runs to the line that repeats it
     *  exactly, which is AsciiDoc's rule and the one the document reader follows — a shorter run
     *  inside a longer one is content rather than the end of it. */
    private static final Pattern LISTING = Pattern.compile("^-{4,}$");

    /**
     * The modules walked are the reserved namespace, not the ones the surface happens to have a
     * name under. Taking them from the surface would drop a module whose last published operation
     * went away, and the section left naming what it used to publish would be the one thing not
     * read — the gap this check exists to close, one level up.
     */
    @Test
    void eachModuleSectionNamesTheOperationsItsModulePublishes() {
        SpecDocument spec = SpecDocument.bundled();
        Map<String, Set<String>> published = publishedByModule();
        Map<String, Set<String>> publishes = new LinkedHashMap<>();
        Map<String, Set<String>> listed = new LinkedHashMap<>();
        for (String module : new TreeSet<>(Reserved.QUALIFIERS)) {
            String anchor = "stdlib-" + module.toLowerCase(Locale.ROOT);
            SpecDocument.Section section = spec.section(anchor);
            assertNotNull(section, "`" + module + "` has no `" + anchor
                    + "` section for a reader to find its operations in");
            publishes.put(module, published.getOrDefault(module, Set.of()));
            listed.put(module, namesListedIn(section.body()));
        }

        assertEquals(render(publishes), render(listed),
                "the specification's list of a module's operations and the module's published"
                        + " surface disagree. The left side is what the library publishes.");
    }

    /**
     * Both sides being empty would compare equal and say nothing, and the walk is over the reserved
     * namespace. That it covers what is published is what makes it the wider of the two to walk;
     * how many modules there are is not written down here.
     */
    @Test
    void thereIsSomethingToCompareSoTheAgreementIsNotBetweenTwoEmptyThings() {
        assertFalse(Reserved.QUALIFIERS.isEmpty(), "no module to compare a section against");
        assertTrue(Reserved.QUALIFIERS.containsAll(publishedByModule().keySet()),
                "a module the library publishes under is a module the walk reaches");
    }

    /** One line per module: its name, then the names it publishes in a fixed order. */
    private static String render(Map<String, Set<String>> byModule) {
        StringJoiner lines = new StringJoiner("\n");
        for (Map.Entry<String, Set<String>> module : byModule.entrySet()) {
            lines.add(module.getKey() + ": " + String.join(" ", module.getValue()));
        }
        return lines.toString();
    }

    /** The published surface, split by the qualifier a caller writes it under. */
    private static Map<String, Set<String>> publishedByModule() {
        Map<String, Set<String>> byModule = new LinkedHashMap<>();
        for (String qualified : DefaultStdlib.get().published()) {
            int dot = qualified.indexOf('.');
            byModule.computeIfAbsent(qualified.substring(0, dot), m -> new TreeSet<>())
                    .add(qualified.substring(dot + 1));
        }
        return byModule;
    }

    /**
     * The names in the section's one block of bare names. A trailing {@code //} comment labels a
     * row — which of them read, which build — and is not part of a name.
     *
     * <p>A name written twice is refused rather than counted once. The comparison that follows is
     * between sets, so a repeat would fold into the name already there and the block would list an
     * operation twice and still agree with the library.
     */
    private static Set<String> namesListedIn(String body) {
        List<List<String>> blocks = new ArrayList<>();
        List<String> current = null;
        String opening = null;
        boolean bare = true;
        for (String line : body.split("\n", -1)) {
            String delimiter = line.strip();
            if (opening == null && LISTING.matcher(delimiter).matches()) {
                opening = delimiter;
                current = new ArrayList<>();
                bare = true;
                continue;
            }
            if (opening != null && delimiter.equals(opening)) {
                // An empty block counts. A module may publish nothing and say so — `Instant` carries
                // what a timestamp said and has no operation at all, which is a rule of that type
                // rather than a section not written yet — and a listing skipped for being empty
                // would leave that module with no block and this check unable to read it.
                if (bare) {
                    blocks.add(current);
                }
                opening = null;
                continue;
            }
            if (opening == null) {
                continue;
            }
            String written = line.split("//", 2)[0].strip();
            if (written.isEmpty()) {
                continue;
            }
            if (!NAME_ROW.matcher(written).matches()) {
                bare = false;
                continue;
            }
            current.addAll(List.of(written.split(" +")));
        }
        if (blocks.size() != 1) {
            throw new IllegalStateException("a module section lists its operations in one block of"
                    + " bare names; found " + blocks.size());
        }
        Set<String> names = new TreeSet<>();
        for (String name : blocks.get(0)) {
            if (!names.add(name)) {
                throw new IllegalStateException("a module section lists `" + name + "` more than once");
            }
        }
        return names;
    }

    @Test
    void theNamesAreTakenFromTheBlockAndTheLabelOnARowIsNot() {
        assertEquals(new TreeSet<>(Set.of("get", "insert", "remove", "size")), namesListedIn("""
                A `+Map+` is immutable.

                [,text]
                ----
                get                      // read
                insert  remove  size     // build
                ----

                `+get+` answers an optional.
                """));
    }

    @Test
    void aBlockThatIsNotARowOfNamesIsNotTheList() {
        assertEquals(new TreeSet<>(Set.of("map", "filter")), namesListedIn("""
                [,text]
                ----
                [e1, e2, ...]
                ----

                [,text]
                ----
                map  filter
                ----
                """));
    }

    @Test
    void aSecondBlockOfBareNamesIsRefusedRatherThanFoldedIntoTheFirst() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> namesListedIn("""
                        [,text]
                        ----
                        map  filter
                        ----

                        [,text]
                        ----
                        take  drop
                        ----
                        """));

        assertTrue(refused.getMessage().contains("found 2"), refused.getMessage());
    }

    /**
     * Folded into the name already there, a repeat would leave the block naming an operation twice
     * and still agreeing with the library — the set it compares as would be the same set.
     */
    @Test
    void anOperationNamedTwiceIsRefusedRatherThanCountedOnce() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> namesListedIn("""
                        [,text]
                        ----
                        map  filter  fold
                        fold  all
                        ----
                        """));

        assertTrue(refused.getMessage().contains("`fold` more than once"), refused.getMessage());
    }

    /** A block runs to the line that repeats its delimiter exactly. Closing it on a shorter run
     *  would end the block where AsciiDoc reads content, and what follows the false end would be
     *  read as the section around it. */
    @Test
    void aShorterRunInsideALongerDelimiterIsContent() {
        assertEquals(new TreeSet<>(Set.of("map", "filter")), namesListedIn("""
                [,text]
                -----
                [e1, e2, ...]
                ----
                not a row of names either
                -----

                [,text]
                ----
                map  filter
                ----
                """));
    }
}
