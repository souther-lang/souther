package souther.compiler.codegen;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignatures;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;

import java.util.EnumSet;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every kernel a standard-library declaration types as answering a {@code String}, anywhere in its
 * result — bare, or under a {@code List}/{@code Set}/{@code Option}/{@code Map}/tuple it returns —
 * either preserves NFC by construction or establishes it, the disjoint union {@code Strings.nfc}'s
 * three kinds of caller split into. Written as a closed-world check over a mechanically-derived
 * population rather than three hand-kept sets naming the same kernels a second time, because a hand
 * kept set is exactly the shape that missed four decoder paths before ADR-0096's leaf was written
 * as one method: it looks complete until the next kernel is added beside it.
 *
 * <p>The population is read off {@link KernelSignatures#signatureOf}, the checker's own resolved
 * {@link Type} for what a kernel answers — not a second parse of the {@code .sou} source a kernel's
 * declaration happens to be written in, which would be a fourth reader of the same fact next to the
 * checker, the codegen table and the stdlib loader. A {@code Type} is walked structurally through
 * {@link Type.ListOf}/{@link Type.SetOf}/{@link Type.OptionOf}/{@link Type.MapOf}/{@link Type.TupleOf}
 * rather than matched by name, so a kernel later declared to answer, say, {@code Option<String>}
 * lands in the population without this file's own list of shapes needing to grow to see it. Not
 * walked into a {@link Type.Union}'s members: none of today's kernels answer one that carries a
 * {@code String}, and resolving what a union member's own declaration is would ask the checker's
 * symbol table a second question this file has no business asking.
 */
class EveryStringProducingKernelPreservesOrEstablishesNfcTest {

    /** {@code PRESERVES}: a substring of an NFC string is NFC (Unicode's own guarantee for
     *  slicing), and every one of these does nothing but select or split code points {@code s}
     *  already has, so no seam is ever created between two pieces that were not already adjacent —
     *  {@code split}/{@code words}/{@code lines}/{@code characters} split into a {@code List<String>}
     *  by the same rule, one piece at a time. */
    private static final Set<Kernel> PRESERVES = EnumSet.of(
            Kernel.STRING_SLICE, Kernel.STRING_TRIM, Kernel.STRING_SPLIT, Kernel.STRING_WORDS,
            Kernel.STRING_LINES, Kernel.STRING_CHARACTERS);

    /** {@code INTRINSICALLY_CANONICAL}: the result is ASCII decimal digits by construction, which
     *  is NFC independent of any input — not because an input invariant is preserved, the way
     *  {@link #PRESERVES} is, but because nothing here reads a code point wide enough to be one. */
    private static final Set<Kernel> INTRINSICALLY_CANONICAL =
            EnumSet.of(Kernel.STRING_FROM_INT, Kernel.STRING_FROM_DECIMAL);

    /** {@code MUST_CANONICALIZE}: a kernel that creates a seam between code points that were not
     *  adjacent before it ran — composition is not closed under concatenation — or that maps a code
     *  point to another one outside the seam ({@code lowercase}/{@code uppercase} can each leave
     *  NFC on their own). Every one canonicalizes its own result in {@code Strings} rather than
     *  trusting a caller to. */
    private static final Set<Kernel> MUST_CANONICALIZE = EnumSet.of(
            Kernel.STRING_APPEND, Kernel.STRING_JOIN, Kernel.STRING_CONCAT, Kernel.STRING_REPLACE,
            Kernel.STRING_REVERSE, Kernel.STRING_REPEAT, Kernel.STRING_LOWERCASE,
            Kernel.STRING_UPPERCASE, Kernel.STRING_PAD_LEFT, Kernel.STRING_PAD_RIGHT);

    @Test
    void everyKernelWhoseResultReachesAStringIsClassifiedExactlyOnce() {
        Stdlib stdlib = DefaultStdlib.get();
        KernelSignatures signatures = stdlib.kernelSignatures();
        Set<Kernel> population = new TreeSet<>();
        for (Kernel kernel : Kernel.values()) {
            if (resultReachesString(signatures.signatureOf(kernel).result())) {
                population.add(kernel);
            }
        }

        Set<Kernel> classified = new TreeSet<>();
        classified.addAll(PRESERVES);
        classified.addAll(INTRINSICALLY_CANONICAL);
        classified.addAll(MUST_CANONICALIZE);

        Set<Kernel> unclassified = new TreeSet<>(population);
        unclassified.removeAll(classified);
        Set<Kernel> classifiedButDoesNotReachString = new TreeSet<>(classified);
        classifiedButDoesNotReachString.removeAll(population);

        assertEquals(Set.of(), unclassified,
                "a kernel whose result reaches String but is in none of PRESERVES,"
                        + " INTRINSICALLY_CANONICAL or MUST_CANONICALIZE — decide which and add it"
                        + " there");
        assertEquals(Set.of(), classifiedButDoesNotReachString,
                "classified here but its result does not reach String — its declaration changed, or"
                        + " this test's classification is stale");

        int overlap = PRESERVES.size() + INTRINSICALLY_CANONICAL.size() + MUST_CANONICALIZE.size()
                - classified.size();
        assertEquals(0, overlap, "a kernel is classified in more than one of the three sets");
    }

    /** Whether {@code type} is {@code String} itself, or reaches one through a container this
     *  language has — the structural walk {@link Type}'s own javadoc describes for
     *  {@code ListOf}/{@code SetOf}/{@code OptionOf}/{@code MapOf} (a map's value; its key is
     *  reached the same way when it is one), plus a tuple's own elements. */
    private static boolean resultReachesString(Type type) {
        return switch (type) {
            case Type.Prim p -> p == Type.STRING;
            case Type.ListOf t -> resultReachesString(t.element());
            case Type.SetOf t -> resultReachesString(t.element());
            case Type.OptionOf t -> resultReachesString(t.element());
            case Type.MapOf t -> resultReachesString(t.key()) || resultReachesString(t.value());
            case Type.TupleOf t -> t.elements().stream().anyMatch(
                    EveryStringProducingKernelPreservesOrEstablishesNfcTest::resultReachesString);
            default -> false;
        };
    }
}
