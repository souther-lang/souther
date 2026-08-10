package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * When a nested value breaks its own invariant during decoding, the reported issue must point at
 * that value's path — not collapse to the document root. Two sibling fields that both violate an
 * invariant used to be indistinguishable because the decoder minted every invariant failure at
 * {@code Path.ROOT}; each now carries the path it was decoded at (spec §violation-destination, §case-propagation).
 */
class CompileInvariantPathTest {

    private static final String MODULE = """
            module demo

            data Amount = Int
                invariant value > 0

            data Order = {
                first: Amount
                , second: Amount
            }
            """;

    private Decoder<Object, ?> orderDecoder() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
        return Codecs.decoder(loader, "demo.Order");
    }

    @Test
    void twoSiblingInvariantViolationsCarryDistinctPaths() throws Exception {
        Result<?> r = orderDecoder().decode(Map.of("first", -1L, "second", -3L), Path.ROOT);
        assertTrue(r instanceof Err, "both fields break value > 0, so decoding must fail");

        List<Issue> issues = ((Err<?>) r).issues().asList();
        Set<String> codes = issues.stream().map(Issue::code).collect(Collectors.toSet());
        // `value > 0` is Raoh's positive() on the leaf, so both carry that constraint's code (#83)
        assertEquals(Set.of("out_of_range"), codes);

        // The two failures must be told apart by their path — first vs second, not both root.
        Set<List<String>> paths = issues.stream()
                .map(i -> i.path().segments())
                .collect(Collectors.toSet());
        assertEquals(Set.of(List.of("first"), List.of("second")), paths,
                "each invariant failure must carry the field it was decoded at");
    }

    @Test
    void aSingleNestedViolationPointsAtItsField() throws Exception {
        Result<?> r = orderDecoder().decode(Map.of("first", 5L, "second", -3L), Path.ROOT);
        assertTrue(r instanceof Err);

        List<Issue> issues = ((Err<?>) r).issues().asList();
        assertEquals(1, issues.size(), "only second breaks the invariant");
        assertEquals("out_of_range", issues.get(0).code());
        assertEquals(1L, issues.get(0).meta().get("min"), "the bound the invariant states");
        assertEquals(-3L, issues.get(0).meta().get("actual"), "the value that broke it");
        assertEquals(List.of("second"), issues.get(0).path().segments());
    }

    @Test
    void aRootValueStillReportsAtRoot() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo
                data Amount = Int
                    invariant value > 0
                """), getClass().getClassLoader());
        Result<?> r = Codecs.decode(loader, "demo.Amount", -1L);
        assertTrue(r instanceof Err);
        assertEquals(List.of(), ((Err<?>) r).issues().asList().get(0).path().segments(),
                "a top-level value keeps the root path");
    }
}
