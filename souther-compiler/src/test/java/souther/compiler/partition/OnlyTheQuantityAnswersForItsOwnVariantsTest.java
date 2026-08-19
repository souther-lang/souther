package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which kind of quantity a border is on is asked where one is made, and nowhere else.
 *
 * <p>This is the arrangement the whole reading turns on, and it is not one a type can hold. A
 * sealed interface stops a variant being added without this file answering for it; nothing stops a
 * reader downstream from switching on which variant it was handed, and that switch is exactly what
 * the shape it replaced cost. A line at a place of one position and a line where two positions stand
 * apart each carried their own criterion vocabulary, border factory, generator entry, probe method,
 * assessment path and report arm — nine places, for the second of two.
 *
 * <p>So the rule is that a reader takes what the quantity answers ({@link BorderQuantity#levels},
 * {@link BorderQuantity#standsAt}, {@link BorderQuantity#standingAt}, {@link BorderQuantity#carrier},
 * {@link BorderQuantity#left}, {@link BorderQuantity#writtenAt}, {@link BorderQuantity#shape}) and
 * never asks which one it is. A reader that needs an answer none of those gives is a reader asking
 * for a method on the quantity, not for a variant.
 *
 * <p><b>Where a variant may be named.</b> Its own file, because that is where the answers live; and
 * the readings that build one, because deciding which quantity a rule cut is what those do. Nothing
 * else, in any module.
 *
 * <p>A tripwire and not a proof. It reads the sources, so a variant reached through a helper written
 * elsewhere defeats it — and the helper would be the first thing to add, which is what this fails on.
 */
class OnlyTheQuantityAnswersForItsOwnVariantsTest {

    /**
     * The files that decide which quantity a rule cut, and the quantity's own.
     *
     * <p>Two of them, because deciding is one question with one answer: {@link Cutting} reads a
     * comparison and {@link Partitions} reads what a position's declarations left. The readings that
     * find the comparisons — a body's conditions, a behavior's clauses — used to be on this list and
     * are not: each of them decided a little of it, and a rule written {@code 48 >= 3a + 6b} came out
     * as a border on {@code -3a - 6b} while the same rule in an {@code ensures} came out as no
     * border at all.
     */
    private static final Set<String> MAY_NAME_ONE = Set.of(
            "souther/compiler/partition/BorderQuantity.java",
            "souther/compiler/partition/Cutting.java",
            "souther/compiler/partition/Partitions.java");

    @Test
    void noReaderOutsideTheQuantityAsksWhichQuantityItIs() throws IOException {
        List<String> variants = variantNames();
        assertFalse(variants.isEmpty(), "found no variants — the reading missed the sealed type");

        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> naming = new TreeSet<>();
        for (Path source : sources) {
            String named = source.toString().replace('\\', '/').replaceAll(".*/src/main/java/", "");
            if (MAY_NAME_ONE.contains(named)) {
                continue;
            }
            String code = withoutComments(Files.readString(source, StandardCharsets.UTF_8));
            for (String variant : variants) {
                if (code.contains("BorderQuantity." + variant)
                        || (named.startsWith("souther/compiler/partition/")
                                && code.matches("(?s).*\\b" + variant + "\\b.*"))) {
                    naming.add(named + " names " + variant);
                }
            }
        }
        assertEquals(Set.of(), naming,
                "a reader outside the quantity is asking which quantity a border is on; take what"
                        + " the quantity answers, or give it a method that answers what is wanted");
    }

    /** And the list this reads is the sealed type's own, so a variant added is one it covers without
     *  anybody remembering to add it here. */
    @Test
    void theVariantsThisReadsAreTheOnesTheTypeDeclares() {
        assertTrue(variantNames().contains("OfACoordinate"), variantNames().toString());
        assertEquals(BorderQuantity.class.getPermittedSubclasses().length, variantNames().size());
    }

    private static List<String> variantNames() {
        return java.util.Arrays.stream(BorderQuantity.class.getPermittedSubclasses())
                .map(Class::getSimpleName).toList();
    }

    /**
     * The file with what is written about the code taken out.
     *
     * <p>Prose names a variant all the time and has to: a comment saying which readings build which
     * quantity is the thing that keeps this arrangement legible. What the rule is about is code.
     */
    private static String withoutComments(String text) {
        return text.replaceAll("(?s)/\\*.*?\\*/", "").replaceAll("(?m)//.*$", "");
    }
}
