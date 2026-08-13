package souther.compiler;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.Test;

/**
 * What a boundary writes a {@code Set} and a {@code Map} out as, byte for byte. The members are put
 * in ascending order of their own external representation, so the order follows the members the
 * collection turned out to hold rather than the history of the collection holding them — not which
 * bucket a hash collision put an element in, and not whether the map was decoded or built.
 *
 * <p>Which members it holds is a separate question this does not answer: two elements the language
 * calls equal are one member, and where they are written differently — {@code Decimal}s of one
 * amount and two scales — which one the set kept is not specified, so nothing here asserts it.
 */
class CompileEncodeOrderTest {


    @Test
    void aSetIsWrittenTheSameWhicheverOrderItsMembersArrivedIn() throws Exception {
        // "Aa" and "BB" share a full 32-bit hash, so they sit in one collision bucket, which holds
        // them in the order they were put — the order the input array gave.
        String source = """
                data In = { tags: Set<String> }
                data Out = { tags: Set<String> }
                behavior echo : (i: In) -> Out constructs Out
                let echo (i) = Out { tags = i.tags }
                """;
        String module = "tags";
        assertEquals("{\"tags\":[\"Aa\",\"BB\"]}",
                Crossing.of(source, module, "echo", "{\"tags\":[\"Aa\",\"BB\"]}"));
        assertEquals("{\"tags\":[\"Aa\",\"BB\"]}",
                Crossing.of(source, module, "echo", "{\"tags\":[\"BB\",\"Aa\"]}"));
    }

    @Test
    void aSetOfEnumerationCasesIsWrittenTheSameWhicheverOrderItsMembersArrivedIn() throws Exception {
        // A unit data has no fields, and the generated hashCode folds over the fields from 1, so
        // every unit data in the program hashes to 1. Any Set holding two of them is one bucket.
        String source = """
                data Stage = Won | Lost | Open
                data In = { stages: Set<Stage> }
                data Out = { stages: Set<Stage> }
                behavior echo : (i: In) -> Out constructs Out
                let echo (i) = Out { stages = i.stages }
                """;
        String module = "stages";
        String written = "{\"stages\":[\"Lost\",\"Open\",\"Won\"]}";
        assertEquals(written, Crossing.of(source, module, "echo", "{\"stages\":[\"Won\",\"Lost\",\"Open\"]}"));
        assertEquals(written, Crossing.of(source, module, "echo", "{\"stages\":[\"Open\",\"Won\",\"Lost\"]}"));
    }

    @Test
    void aMapIsWrittenTheSameWhetherItWasDecodedOrBuilt() throws Exception {
        // A map that has been through an insert or a remove is a trie and is walked as one; a
        // decoded map never became one, and is walked as whatever the decode left behind — which is
        // a java.util.ImmutableCollections$MapN, whose iteration order is randomised per JVM by
        // that class's SALT. So the two are the same map written two ways, no hash collision is
        // needed to tell them apart, and the decoded one is not even written the same way twice.
        // Six keys, so that a random permutation matching the order below is a 1-in-720 accident.
        String source = """
                module demo

                import Map ( insert, remove )

                data In = { counts: Map<String, Int> }
                data Out = {
                    asIs: Map<String, Int>
                    , touched: Map<String, Int>
                }
                behavior echo : (i: In) -> Out constructs Out
                let echo (i) = Out {
                    asIs = i.counts,
                    touched = remove("zz", insert("zz", 0, i.counts))
                }
                """;
        String module = "counts";
        String written = "{\"asIs\":{\"a\":1,\"b\":2,\"c\":3,\"d\":4,\"e\":5,\"f\":6},"
                + "\"touched\":{\"a\":1,\"b\":2,\"c\":3,\"d\":4,\"e\":5,\"f\":6}}";
        assertEquals(written, Crossing.of(source, module, "echo",
                "{\"counts\":{\"f\":6,\"d\":4,\"b\":2,\"e\":5,\"a\":1,\"c\":3}}"));
    }

    @Test
    void aNestedCollectionIsOrderedAtEveryDepth() throws Exception {
        String source = """
                data In = { byOwner: Map<String, Set<String>> }
                data Out = { byOwner: Map<String, Set<String>> }
                behavior echo : (i: In) -> Out constructs Out
                let echo (i) = Out { byOwner = i.byOwner }
                """;
        String module = "nested";
        assertEquals("{\"byOwner\":{\"a\":[\"y\",\"z\"],\"b\":[\"Aa\",\"BB\"]}}",
                Crossing.of(source, module, "echo",
                        "{\"byOwner\":{\"b\":[\"BB\",\"Aa\"],\"a\":[\"z\",\"y\"]}}"));
    }

    @Test
    void twoSetsThatAreOneValueAreWrittenTheOneWay() throws Exception {
        // The last way the order could not reach. `1.0` and `1.00` are one amount, so a Set holds
        // one of them and which one is whichever arrived first — no ordering can separate members
        // that are one member. What closes it is that a boundary writes an amount as an amount
        // ([#primitives]), which makes the two sets the same bytes rather than the same order.
        //
        // Driven through the derived codecs rather than `souther run`, because the runner's JSON
        // parser reads a float as a double and the scale is gone before a decoder sees it.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { amounts: Set<Decimal> }
                data Out = { amounts: Set<Decimal> }
                behavior echo : (i: In) -> Out constructs Out
                let echo (i) = Out { amounts = i.amounts }
                """), getClass().getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "echo").getConstructor().newInstance();

        assertEquals(written(loader, behavior, new BigDecimal("1.0"), new BigDecimal("1.00")),
                written(loader, behavior, new BigDecimal("1.00"), new BigDecimal("1.0")),
                "the set keeps one of the two and the boundary writes it as its amount");
        assertEquals(List.of(new BigDecimal("1"), new BigDecimal("2.5")),
                written(loader, behavior, new BigDecimal("2.50"), new BigDecimal("1.00")),
                "and the amounts are what the members are ordered by");
    }

    private Object written(BytesClassLoader loader, Object behavior, BigDecimal... amounts)
            throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", Map.of("amounts", List.of((Object[]) amounts)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        return out.get("amounts");
    }
}
