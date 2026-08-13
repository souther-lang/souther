package souther.compiler;

import souther.compiler.diag.msg.NameMessage;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** The Set standard library ([#stdlib-set]): building and the set algebra, exercised in a behavior
 *  body (a Set is not yet a data field until its codec lands). */
class CompileSetLibTest {

    @Test
    void buildAndCombineSets() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Set ( singleton, insert, contains, union, intersection, difference, size, isEmpty, toList, fromList )

                data In = { xs: List<String> }
                data Out = {
                    n: Int
                    , hasA: Bool
                    , unionList: List<String>
                    , interList: List<String>
                    , diffList: List<String>
                    , emptyFlag: Bool
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let s = insert("c", insert("b", insert("a", Set.empty)))
                    let t = fromList(i.xs)
                    Out {
                        n = size(s),
                        hasA = contains("a", s),
                        unionList = toList(union(s, t)),
                        interList = toList(intersection(s, t)),
                        diffList = toList(difference(s, t)),
                        emptyFlag = isEmpty(Set.empty)
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("xs", List.of("b", "d")));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(3L, m.get("n"), "the set {a, b, c} has three members");
        assertEquals(true, m.get("hasA"));
        // What the algebra answers is a membership question, so that is what these assert. The order
        // the boundary writes them in is a separate contract, pinned in CompileEncodeOrderTest.
        assertEquals(Set.of("a", "b", "c", "d"), Set.copyOf((List<?>) m.get("unionList")));
        assertEquals(Set.of("b"), Set.copyOf((List<?>) m.get("interList")));
        assertEquals(Set.of("a", "c"), Set.copyOf((List<?>) m.get("diffList")));
        assertEquals(true, m.get("emptyFlag"));
    }

    /** The higher-order operations go out through {@code toList} and back through {@code fromList},
     *  so {@code List.fold} stays the one loop. {@code map} may shrink the set: two elements that
     *  land on the same image collapse. */
    @Test
    void mapFilterFoldAndPartitionOverASet() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Set ( fromList, toList, map, filter, fold, partition, size )

                data In = { xs: List<String> }
                data Out = {
                    upper: List<String>
                    , kept: List<String>
                    , joined: String
                    , yes: List<String>
                    , no: List<String>
                    , collapsed: Int
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let s = fromList(i.xs)
                    let (a, b) = partition(x -> String.startsWith("a", x), s)
                    Out {
                        upper = toList(map(x -> String.uppercase(x), s)),
                        kept = toList(filter(x -> String.length(x) == 2, s)),
                        joined = fold((acc, x) -> acc ++ x, "", Set.map(x -> "-", s)),
                        yes = toList(a),
                        no = toList(b),
                        collapsed = size(Set.map(x -> String.slice(0, 1, x), s))
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("xs", List.of("ab", "ac", "bd")));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, in));

        assertEquals(Set.of("AB", "AC", "BD"), Set.copyOf((List<?>) m.get("upper")));
        assertEquals(Set.of("ab", "ac", "bd"), Set.copyOf((List<?>) m.get("kept")));
        // `map` onto one image collapses the whole set to a single element, so the fold sees one "-".
        assertEquals("-", m.get("joined"));
        assertEquals(Set.of("ab", "ac"), Set.copyOf((List<?>) m.get("yes")));
        assertEquals(Set.of("bd"), Set.copyOf((List<?>) m.get("no")));
        assertEquals(2L, m.get("collapsed"), "ab and ac share the first letter, so {a, b} is left");
    }

    /** The empty set is a value, for the reason the empty map is: no parameter list, no argument list. */
    @Test
    void applyingTheEmptySetIsRefusedAsApplyingAValue() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Out = { s: Set<String> }
                data Req = { n: Int }
                behavior go : (r: Req) -> Out
                    constructs Out
                let go (r) = Out { s = Set.empty() }
                """));
        assertInstanceOf(NameMessage.ItIsNotAFunctionHere.class, e.diagnostic().said());
    }
}
