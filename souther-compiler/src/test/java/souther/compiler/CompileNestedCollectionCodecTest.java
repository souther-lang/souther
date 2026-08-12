package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A collection may hold a collection at the boundary: {@code Map<String, List<商品ID>>} is what
 * bucketing rows by a key produces ({@code List.groupBy}), and it has to encode as well as it
 * decodes. The derived decoder already recursed; these fix that the derived encoder does too, for
 * every nesting the type system allows — including the two shapes that are not Raoh combinators on
 * their own, a nested Set (listed first) and a nested newtype-keyed Map (keys rendered bare first).
 */
class CompileNestedCollectionCodecTest {

    private static final String MODULE = """
            module demo

            data 商品ID = String
            data ラベル = String

            data In = {
                byOwner: Map<String, List<商品ID>>
                , tags: Map<String, Set<ラベル>>
                , stocks: List<Map<商品ID, Int>>
                , grid: List<List<Int>>
            }
            data Out = {
                byOwner: Map<String, List<商品ID>>
                , tags: Map<String, Set<ラベル>>
                , stocks: List<Map<商品ID, Int>>
                , grid: List<List<Int>>
            }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = Out {
                byOwner = i.byOwner,
                tags = i.tags,
                stocks = i.stocks,
                grid = i.grid
            }
            """;

    @Test
    void nestedCollectionsRoundTrip() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of(
                "byOwner", Map.of("kawasima", List.of("P-01", "P-02")),
                "tags", Map.of("bug", List.of("urgent", "ui")),
                "stocks", List.of(Map.of("P-01", 3L), Map.of("P-02", 5L)),
                "grid", List.of(List.of(1L, 2L), List.of(3L))));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("kawasima", List.of("P-01", "P-02")), m.get("byOwner"),
                "a list under a map value is encoded element by element, the newtype bare");
        assertEquals(List.of(Map.of("P-01", 3L), Map.of("P-02", 5L)), m.get("stocks"),
                "a newtype-keyed map inside a list still renders its keys bare");
        assertEquals(List.of(List.of(1L, 2L), List.of(3L)), m.get("grid"));

        // A Set is written as an array, its members in ascending order of their own external
        // representation ([#collections]) — at this depth as at any other.
        Map<?, ?> tags = (Map<?, ?>) m.get("tags");
        assertEquals(List.of("ui", "urgent"), tags.get("bug"),
                "a set under a map value is listed, then each element encoded");
    }
}
