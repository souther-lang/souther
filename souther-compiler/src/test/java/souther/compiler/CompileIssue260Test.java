package souther.compiler;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two models that found this, kept as they were reported.
 *
 * <p>Each asked one question four ways and got four answers. What made them worth reporting is that
 * neither failed: the model compiled, the tests over well-formed data passed, and the rule the model
 * stated was simply absent.
 */
class CompileIssue260Test {

    private static final String DECIMALS = """
            module demo

            data Row = { rate: Decimal }
            data Req = { rows: List<Row> }
            data Out =
                { equalUnderMember: Bool
                , distinctCount: Int
                , setSize: Int
                , allUnique: Bool
                }
            behavior go : (r: Req) -> Out
                constructs Out
            let go (r) = {
                let rates = List.map(x -> x.rate, r.rows)
                Out { equalUnderMember =
                        List.contains(List.get(0, rates) |> Option.withDefault(0.0m),
                                    List.drop(1, rates))
                    , distinctCount = List.length(List.distinct(rates))
                    , setSize = Set.size(Set.fromList(rates))
                    , allUnique = List.allDistinctBy(x -> x.rate, r.rows)
                    }
            }
            """;

    private static final String TRANSITIONS = """
            module demo

            data Transition = { from: String, event: String, to: String }
            data Machine = { transitions: List<Transition> }
                invariant deterministic = List.allDistinctBy(t -> (t.from, t.event), transitions)
            data Out = { n: Int }
            behavior load : (m: Machine) -> Out
                constructs Out
            let load (m) = Out { n = List.length(m.transitions) }
            """;

    private Object row(String rate) {
        Map<String, Object> r = new LinkedHashMap<>();
        r.put("rate", new BigDecimal(rate));
        return r;
    }

    private Map<String, Object> transition(String from, String event, String to) {
        Map<String, Object> t = new LinkedHashMap<>();
        t.put("from", from);
        t.put("event", event);
        t.put("to", to);
        return t;
    }

    /** A machine decoded from its transitions: {@code Ok} when the invariant holds, {@code Err}
     *  naming the clause when it does not. The rule is stated on the data, so the boundary is where
     *  it is answered. */
    private Result<?> machine(Object... transitions) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(TRANSITIONS), getClass().getClassLoader());
        Map<String, Object> raw = new LinkedHashMap<>();
        raw.put("transitions", List.of(transitions));
        return Codecs.decode(loader, "demo.Machine", raw);
    }

    /** One pair of amounts, asked four ways: they were 1.0 and 1, and only `member` said so. */
    @Test
    void oneAmountAtTwoScalesIsOneAmountToAllFour() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(DECIMALS), getClass().getClassLoader());
        Map<String, Object> raw = new LinkedHashMap<>();
        raw.put("rows", List.of(row("1.0"), row("1")));
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.Req", raw)));

        assertEquals(true, out.get("equalUnderMember"));
        assertEquals(1L, ((Number) out.get("distinctCount")).longValue());
        assertEquals(1L, ((Number) out.get("setSize")).longValue());
        assertEquals(false, out.get("allUnique"));
    }

    /** "One row per (from, event)" is a rule now; it used to hold of everything. */
    @Test
    void aCompositeUniquenessRuleRejectsARepeatedPair() throws Exception {
        assertFalse(machine(transition("new", "submit", "open"),
                transition("new", "submit", "shut")) instanceof Ok<?>);
    }

    @Test
    void andAdmitsRowsThatDifferInEitherPart() throws Exception {
        assertTrue(machine(transition("new", "submit", "open"),
                transition("new", "cancel", "shut")) instanceof Ok<?>);
        assertTrue(machine(transition("new", "submit", "open"),
                transition("open", "submit", "shut")) instanceof Ok<?>);
    }
}
