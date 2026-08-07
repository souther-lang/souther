package souther.compiler.doc;

import souther.compiler.Prelude;

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

    /** The listing delimiter, as the document writes it. */
    private static final Pattern LISTING = Pattern.compile("^-{4,}$");

    @Test
    void eachModuleSectionNamesTheOperationsItsModulePublishes() {
        SpecDocument spec = SpecDocument.bundled();
        Map<String, Set<String>> listed = new LinkedHashMap<>();
        for (String module : publishedByModule().keySet()) {
            String anchor = "stdlib-" + module.toLowerCase(Locale.ROOT);
            SpecDocument.Section section = spec.section(anchor);
            assertNotNull(section, "`" + module + "` publishes names and has no `" + anchor
                    + "` section for a reader to find them in");
            listed.put(module, namesListedIn(section.body()));
        }

        assertEquals(render(publishedByModule()), render(listed),
                "the specification's list of a module's operations and the module's published"
                        + " surface disagree. The left side is what the library publishes.");
    }

    /**
     * Both sides being empty would compare equal and say nothing. The count is the ten modules the
     * document has a section for; a new one arrives with a section or fails the check above.
     */
    @Test
    void everyModuleIsComparedSoTheAgreementIsNotBetweenTwoEmptyThings() {
        Map<String, Set<String>> published = publishedByModule();

        assertEquals(10, published.size(), "every published module is compared: " + published.keySet());
        assertTrue(published.get("List").contains("zipShortest"),
                "the library publishes the name the block is checked against");
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
        for (String qualified : Prelude.published()) {
            int dot = qualified.indexOf('.');
            byModule.computeIfAbsent(qualified.substring(0, dot), m -> new TreeSet<>())
                    .add(qualified.substring(dot + 1));
        }
        return byModule;
    }

    /**
     * The names in the section's one block of bare names. A trailing {@code //} comment labels a
     * row — which of them read, which build — and is not part of a name.
     */
    private static Set<String> namesListedIn(String body) {
        List<Set<String>> blocks = new ArrayList<>();
        Set<String> current = null;
        boolean inside = false;
        boolean bare = true;
        for (String line : body.split("\n", -1)) {
            if (LISTING.matcher(line.strip()).matches()) {
                if (inside) {
                    if (bare && current != null && !current.isEmpty()) {
                        blocks.add(current);
                    }
                    inside = false;
                } else {
                    inside = true;
                    bare = true;
                    current = new TreeSet<>();
                }
                continue;
            }
            if (!inside) {
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
        return blocks.get(0);
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
}
