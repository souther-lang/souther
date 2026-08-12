package souther.compiler;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The same amount at two scales is one value in every shape the language can put it in, and a
 * hash-based container agrees. Each row asks twice: whether {@code ==} says they are one value, and
 * whether a {@code Set} built from both holds one element — the second is what says the hash agrees
 * with the equality, which is the half that goes wrong on its own.
 *
 * <p>The rows are the type constructors, not the classes that implement them. A container added to
 * the runtime later is covered by the row its shape already has, and a type constructor added to the
 * language is one the capability table will not compile until it is answered for — at which point
 * this table is where it is answered again, in values.
 */
class CompileValueEqualityMatrixTest {

    private static final String MODULE = """
            module demo

            data Amount = Decimal
            data Row = { rate: Decimal }
            data Req = { a: Decimal, b: Decimal }
            data Out =
                { decimalEq: Bool,   decimalSet: Int
                , newtypeEq: Bool,   newtypeSet: Int
                , dataEq: Bool,      dataSet: Int
                , listEq: Bool,      listSet: Int
                , optionEq: Bool,    optionSet: Int
                , tupleEq: Bool,     tupleSet: Int
                , setEq: Bool,       setSet: Int
                , mapValueEq: Bool,  mapValueSet: Int
                , mapKeyEq: Bool,    mapKeySet: Int
                }

            behavior go : (r: Req) -> Out
                constructs Out, Row, Amount
            let go (r) = {
                // an optional is read, never built (E1303), so the two come out of a Map
                let oa = Map.get("k", Map.insert("k", r.a, Map.empty))
                let ob = Map.get("k", Map.insert("k", r.b, Map.empty))
                let sa = Set.fromList([r.a])
                let sb = Set.fromList([r.b])
                let mva = Map.insert("k", r.a, Map.empty)
                let mvb = Map.insert("k", r.b, Map.empty)
                let mka = Map.insert(r.a, 1, Map.empty)
                let mkb = Map.insert(r.b, 1, Map.empty)
                Out { decimalEq   = r.a == r.b
                    , decimalSet  = Set.size(Set.fromList([r.a, r.b]))
                    , newtypeEq   = Amount(r.a) == Amount(r.b)
                    , newtypeSet  = Set.size(Set.fromList([Amount(r.a), Amount(r.b)]))
                    , dataEq      = Row { rate = r.a } == Row { rate = r.b }
                    , dataSet     = Set.size(Set.fromList([Row { rate = r.a }, Row { rate = r.b }]))
                    , listEq      = [r.a] == [r.b]
                    , listSet     = Set.size(Set.fromList([[r.a], [r.b]]))
                    , optionEq    = oa == ob
                    , optionSet   = Set.size(Set.fromList([oa, ob]))
                    , tupleEq     = (r.a, "x") == (r.b, "x")
                    , tupleSet    = Set.size(Set.fromList([(r.a, "x"), (r.b, "x")]))
                    , setEq       = sa == sb
                    , setSet      = Set.size(Set.fromList([sa, sb]))
                    , mapValueEq  = mva == mvb
                    , mapValueSet = Set.size(Set.fromList([mva, mvb]))
                    , mapKeyEq    = mka == mkb
                    , mapKeySet   = Set.size(Set.fromList([mka, mkb]))
                    }
            }
            """;

    private Map<?, ?> answers() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
        Map<String, Object> raw = new LinkedHashMap<>();
        raw.put("a", new BigDecimal("1.0"));
        raw.put("b", new BigDecimal("1"));
        Object in = Codecs.decoded(loader, "demo.Req", raw);
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    @Test
    void everyEqualityBearingConstructorAgreesWithItsHash() throws Exception {
        Map<?, ?> out = answers();
        for (String shape : new String[] {"decimal", "newtype", "data", "list", "option", "tuple",
                "set", "mapValue", "mapKey"}) {
            assertEquals(true, out.get(shape + "Eq"), shape + ": one amount at two scales");
            assertEquals(1L, ((Number) out.get(shape + "Set")).longValue(),
                    shape + ": the hash agrees with the equality");
        }
    }

    private static final String BOUNDARY = """
            module demo

            data Req = { rates: Set<Decimal> }
            data Out = { n: Int }
            behavior go : (r: Req) -> Out
                constructs Out
            let go (r) = Out { n = Set.size(r.rates) }
            """;

    /**
     * A Set field is deduplicated on decode, which is the earliest the rule can be wrong: a set that
     * held both amounts would arrive already not being what its own type says it is, before a
     * behavior had run at all.
     */
    @Test
    void aSetFieldIsDeduplicatedOnDecode() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(BOUNDARY), getClass().getClassLoader());
        Map<String, Object> raw = new LinkedHashMap<>();
        raw.put("rates", java.util.List.of(new BigDecimal("1.0"), new BigDecimal("1")));
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.Req", raw)));
        assertEquals(1L, ((Number) out.get("n")).longValue());
    }
}
