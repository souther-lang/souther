package souther.compiler.check;

import net.unit8.notation199x.Normalization;
import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an operation said to keep whether a string holds a code point that is not whitespace
 * answers holds one exactly where the string does, asked of every code point.
 *
 * <p>The run that holds every axiom about a kernel to what it computes
 * ({@link EveryAxiomAboutAKernelHoldsOfWhatItComputesTest}) hands a string a few values, and a case
 * mapping is defined code point by code point. A mapping takes each code point to some, and the
 * composition after it joins code points into one that is whitespace only where they were; so a
 * string holds one that is not where one of its code points does, and each code point is asked
 * here — through the runtime's own operation, and the alphabet {@code String.words} scans with.
 *
 * <p>Strings put end to end are canonical at the seams, which is the same composition. Composing
 * is the inverse of decomposing, so where the canonical decomposition of every code point holds
 * one that is not whitespace exactly where the code point is not, decomposing and composing again
 * keep whether a string holds one — whatever stands either side of a seam. That is asked of every
 * code point too.
 *
 * <p>The operations asked are the ones the library says keep it. Each is one this knows how to
 * run, and one added fails here until this says how.
 */
class EveryCodePointKeepsWhetherItIsWhitespaceThroughACaseMappingTest {

    private static final Map<String, UnaryOperator<String>> RUN = Map.of(
            "String.lowercase", Strings::lowercase,
            "String.uppercase", Strings::uppercase,
            "String.trim", Strings::trim,
            "String.concat", one -> Strings.concat(List.of(one)));

    /** Of the operations {@link #RUN} runs, those that keep it of some element of the strings
     *  they take rather than of the string. */
    private static final Set<String> OF_SOME_ELEMENT = Set.of("String.concat");

    @Test
    void everyCodePointThatIsNotWhitespaceIsKeptAndNoOtherIsMade() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Set<String> declared = new TreeSet<>();
        for (ValueName.Stdlib.Operation operation : DefaultStdlib.get().entries().keySet()) {
            if (facts.keepsWhetherItHoldsACodePointOf(operation)
                    instanceof BoundOperationFacts.KeptCodePoints kept) {
                assertEquals(new CodePointClass.NotWhitespace(), kept.counted(),
                        operation.qualified() + " keeps what this asks");
                assertEquals(0, kept.string().position(),
                        operation.qualified() + " keeps it of the one argument it reads");
                assertEquals(OF_SOME_ELEMENT.contains(operation.qualified())
                                ? BoundOperationFact.KeepsWhetherItHoldsACodePointOf.HeldBy
                                        .SOME_ELEMENT
                                : BoundOperationFact.KeepsWhetherItHoldsACodePointOf.HeldBy
                                        .THE_STRING,
                        kept.held(), operation.qualified() + " keeps it of what this runs");
                declared.add(operation.qualified());
            }
        }
        assertEquals(new TreeSet<>(RUN.keySet()), declared,
                "each operation said to keep it is one this runs");
        List<String> wrong = new ArrayList<>();
        for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
            if (Character.getType(cp) == Character.SURROGATE) {
                continue;
            }
            String one = Character.toString(cp);
            boolean holds = !Strings.words(one).isEmpty();
            int at = cp;
            // A string an operation hands back unchanged holds what it held, so only a code point
            // the operation changes is scanned again.
            RUN.forEach((name, run) -> {
                String ran = run.apply(one);
                if (!ran.equals(one) && Strings.words(ran).isEmpty() == holds) {
                    wrong.add(name + " of U+" + Integer.toHexString(at));
                }
            });
            String decomposed = Normalization.normalize(Normalization.Form.NFD, one);
            if (!decomposed.equals(one) && Strings.words(decomposed).isEmpty() == holds) {
                wrong.add("the canonical decomposition of U+" + Integer.toHexString(at));
            }
        }
        assertEquals(List.of(), wrong);
    }
}
