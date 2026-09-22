package souther.compiler.codegen;

import org.junit.jupiter.api.Test;
import souther.compiler.Reserved;
import souther.compiler.check.StdlibLoader;
import souther.compiler.core.Kernel;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every kernel a standard-library declaration types as returning bare {@code String} either
 * preserves NFC by construction or establishes it — the disjoint union {@code Strings.nfc}'s three
 * kinds of caller split into. Written as a closed-world check over a mechanically-derived
 * population rather than three hand-kept sets naming the same kernels a second time, because a hand
 * kept set is exactly the shape that missed four decoder paths before ADR-0096's leaf was written
 * as one method: it looks complete until the next kernel is added beside it.
 *
 * <p>The population comes from the standard library's own {@code intrinsic} declarations, scanned
 * from the {@code .sou} resources every module is loaded from — not from {@link Kernel#values()}
 * filtered by name, since a kernel's key is not something read back into an operation
 * ({@link Kernel}'s own javadoc). A kernel already in hand from {@link Kernel#values()} is checked
 * against what its own declaration says it returns; nothing here turns a key string into a kernel.
 */
class EveryStringProducingKernelPreservesOrEstablishesNfcTest {

    /** A function's own declaration line: {@code let <name> (<params>): <type> = intrinsic "<key>"}. */
    private static final Pattern INTRINSIC_DECLARATION = Pattern.compile(
            "let\\s+[a-zA-Z][a-zA-Z0-9]*\\s*\\([^)]*\\)\\s*:\\s*([^=]+?)\\s*=\\s*intrinsic\\s+\"([a-z][a-zA-Z0-9.]*)\"");

    /** {@code PRESERVES}: a substring of an NFC string is NFC (Unicode's own guarantee for
     *  slicing), and every one of these does nothing but select code points {@code s} already has,
     *  so no seam is ever created between two pieces that were not already adjacent. {@code split},
     *  {@code words}, {@code lines} and {@code characters} apply the same guarantee but are outside
     *  this population: each returns {@code List<String>}, not a bare {@code String}. */
    private static final Set<Kernel> PRESERVES = EnumSet.of(Kernel.STRING_SLICE, Kernel.STRING_TRIM);

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
    void everyKernelDeclaredToReturnStringIsClassifiedExactlyOnce() {
        Map<String, String> returnTypeByKey = declaredReturnTypesByIntrinsicKey();
        Set<Kernel> population = new TreeSet<>();
        for (Kernel kernel : Kernel.values()) {
            if ("String".equals(returnTypeByKey.get(kernel.key()))) {
                population.add(kernel);
            }
        }

        Set<Kernel> classified = new TreeSet<>();
        classified.addAll(PRESERVES);
        classified.addAll(INTRINSICALLY_CANONICAL);
        classified.addAll(MUST_CANONICALIZE);

        Set<Kernel> unclassified = new TreeSet<>(population);
        unclassified.removeAll(classified);
        Set<Kernel> classifiedButNotStringProducing = new TreeSet<>(classified);
        classifiedButNotStringProducing.removeAll(population);

        assertEquals(Set.of(), unclassified,
                "declared to return String but not in PRESERVES, INTRINSICALLY_CANONICAL or"
                        + " MUST_CANONICALIZE — decide which and add it there");
        assertEquals(Set.of(), classifiedButNotStringProducing,
                "classified here but not declared to return String — its declaration changed, or"
                        + " this test's classification is stale");

        int overlap = PRESERVES.size() + INTRINSICALLY_CANONICAL.size() + MUST_CANONICALIZE.size()
                - classified.size();
        assertEquals(0, overlap, "a kernel is classified in more than one of the three sets");
    }

    /** Every kernel's key mapped to what its own {@code .sou} declaration types its result as,
     *  scanned from the standard library's own resources rather than from {@link Kernel} — which
     *  {@link Kernel}'s javadoc says cannot answer this the other way around. */
    private static Map<String, String> declaredReturnTypesByIntrinsicKey() {
        Map<String, String> byKey = new LinkedHashMap<>();
        for (Reserved.StdlibModule module : Reserved.MODULES) {
            String resource = "/" + module.moduleName().replace('.', '/') + ".sou";
            String source = readResource(resource);
            Matcher m = INTRINSIC_DECLARATION.matcher(source);
            while (m.find()) {
                byKey.put(m.group(2), m.group(1).trim());
            }
        }
        return byKey;
    }

    private static String readResource(String resource) {
        try (InputStream in = StdlibLoader.class.getResourceAsStream(resource)) {
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
