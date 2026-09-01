package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which orders a term stands on is worked out in one place, from what one reading resolved.
 *
 * <p>A term is a value that travels and a type is in every reader's hand, so anything that can put
 * the two together can answer what a number is measured on — about wherever that type came from,
 * and about no reading in particular. The answer is right only while the type the caller holds and
 * the type the reading resolved agree, and nothing says when they stop agreeing.
 *
 * <p>Which is why the derivation is package-private here and the way to it is
 * {@link Quantities#ordersOf}. Visibility settles who may call it; it does not settle how many
 * places inside this package do, and a second one is the same defect written where the compiler
 * cannot see it. So this counts them.
 *
 * <p><b>Counted in the sources rather than declared in a list.</b> A list of allowed callers is a
 * thing to keep up to date, and the first person to add one keeps it up to date by adding
 * themselves. The count is what the rule says.
 */
class OneReadingAnswersWhatATermIsMeasuredOnTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** Where both orders of a term are worked out from a type. */
    private static final String DERIVED = "TermOrdering.of(";

    @Test
    void oneProductionPlaceDerivesATermsOrders() throws IOException {
        List<Path> sources = REPOSITORY.mainJavaSources();
        assertTrue(sources.size() > 20,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> derives = new ArrayList<>();
        for (Path source : sources) {
            String text = code(Files.readString(source, StandardCharsets.UTF_8));
            if (text.contains(DERIVED) && !source.getFileName().toString().equals("TermOrdering.java")) {
                derives.add(source.getParent().getFileName() + "/" + source.getFileName());
            }
        }

        assertEquals(List.of("inputs/ReadQuantities.java"), derives,
                "a term's orders are worked out where the reading that resolved its subject is,"
                        + " and a second place is a reader answering for a reading of its own");
    }

    /**
     * And the way in stays shut, which is what makes the count above the whole of the rule.
     *
     * <p>Asked of the class rather than of the sources. What stops a reader elsewhere from pairing
     * two carriers of its own is that it cannot name the constructor, and that is a property of
     * {@link TermOrders} rather than of anything written at a call site — widen either of these and
     * every source in the compiler may make one, with nothing else here failing.
     */
    @Test
    void theWayToMakeAPairIsNotOpenToOtherPackages() {
        for (java.lang.reflect.Constructor<?> made : TermOrders.class.getDeclaredConstructors()) {
            assertTrue(!java.lang.reflect.Modifier.isPublic(made.getModifiers()),
                    () -> "a term's orders are made from what a reading resolved, and " + made
                            + " lets any caller pair two carriers it happens to hold");
        }
        assertTrue(java.util.Arrays.stream(TermOrders.class.getDeclaredMethods())
                        .filter(each -> each.getReturnType() == TermOrders.class)
                        .noneMatch(each ->
                                java.lang.reflect.Modifier.isPublic(each.getModifiers())),
                "and no factory beside it is open either");
    }

    /** {@code source} with its comments taken out, which is what this reads: a file may say what
     *  the rule is without being a place that does it. */
    private static String code(String source) {
        return source.replaceAll("(?s)/\\*.*?\\*/", " ").replaceAll("//[^\n]*", " ");
    }
}
