package souther.compiler.numeric;

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

/**
 * Which values a form {@code Σ cᵢ·xᵢ} can add up to is derived in one place.
 *
 * <p>It had been derived in two, and the two disagreed. Asked of a border, {@code 3 * a} over
 * decimals does not come to one, and the report was right to refuse a row there. Asked of the
 * interval algebra, {@code 3 * a = 1} came back as a satisfiable range around a third — a range
 * whose ends are two decimals neither of which is a third, describing a value no model can write.
 * Two answers about one piece of arithmetic, and the layer that got it wrong is the one whose bounds
 * everything downstream reads.
 *
 * <p>What was duplicated is small and is exactly the part that is easy to get subtly wrong: the
 * divisor the coefficients share, and which factors are units among the finite decimals. So the rule
 * is that {@link AdditiveImage} derives both and everything else asks it.
 *
 * <p>A tripwire and not a proof. It reads the sources, so the same arithmetic spelled a new way
 * defeats it — and spelling it a new way is what the second implementation was.
 */
class OnePlaceDerivesWhatAFormCanAddUpToTest {

    /**
     * Where this arithmetic may be written: the type that answers for it, and the ratio type whose
     * lowest terms it is built out of.
     *
     * <p>Both in this package, which is the point — the partition layer used to hold a copy, and a
     * copy there is one the interval algebra cannot reach and so cannot agree with.
     */
    private static final Set<String> MAY_DERIVE_IT = Set.of(
            "souther/compiler/numeric/AdditiveImage.java",
            "souther/compiler/numeric/Rational.java");

    /** Taking the factors of ten out of a number, which is what makes a divisor over the finite
     *  decimals canonical. Two and five named together in one file is what the copy looked like. */
    @Test
    void theUnitsOfTheFiniteDecimalsAreTakenOutInOnePlace() throws IOException {
        assertEquals(Set.of(), sourcesMatching(code ->
                        code.contains("BigInteger.TWO") && code.contains("valueOf(5)")),
                "ten is a unit among the finite decimals and so are two and five; a second place"
                        + " deciding that is a second answer to which values a form reaches");
    }

    /** And the divisor the coefficients share, which is the other half of the same answer. */
    @Test
    void theDivisorCoefficientsShareIsFoundInOnePlace() throws IOException {
        assertEquals(Set.of(), sourcesMatching(code -> code.contains("Rational.gcd(")),
                "the divisor of a form's coefficients is what its values are multiples of; ask"
                        + " AdditiveImage for it rather than folding one alongside");
    }

    private static Set<String> sourcesMatching(java.util.function.Predicate<String> holds)
            throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");
        Set<String> found = new TreeSet<>();
        for (Path source : sources) {
            String named = source.toString().replace('\\', '/').replaceAll(".*/src/main/java/", "");
            if (MAY_DERIVE_IT.contains(named)) {
                continue;
            }
            if (holds.test(withoutComments(Files.readString(source, StandardCharsets.UTF_8)))) {
                found.add(named);
            }
        }
        return found;
    }

    /** The file with what is written about the code taken out. Prose has to be able to say what the
     *  rule is; what the rule is about is code. */
    private static String withoutComments(String text) {
        return text.replaceAll("(?s)/\\*.*?\\*/", "").replaceAll("(?m)//.*$", "");
    }
}
