package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a body holds is settled without asking where any rule it is judged against is written.
 *
 * <p>The boundary itself rather than what is on either side of it. {@link ClauseLocations} says a
 * place is looked up by the reader that is about to point somewhere and by nobody else, and what
 * makes that true of a check is that nothing it reads, however far down, is an answer about where a
 * clause is. A check that read one would keep its answer only for as long as nobody moved a clause
 * it judged — which is a report going stale or a body being checked again, and it is not visible in
 * anything the compiler says.
 *
 * <p>Held of the reading, not of the name. What the question is called and which file it is written
 * in decide nothing here: this walks what the answer actually read and asks whether a place is among
 * it.
 *
 * <p>The comparison beside it is what keeps this from passing on a workspace where nothing asks
 * about a place at all. The warning about the same construction does ask, because pointing at the
 * rule is what it is for.
 *
 * <p>Of a body the check accepts. A construction the check proves must fail is refused where it is
 * met, and the refusal is said there because it is what stops the check — there is no answer about
 * that body for a later reader to be pointing from, the answer being that it has no meaning to emit.
 * So a refused body does read where the clause it names is written, and what that costs is the check
 * of a body nothing compiles being run again when a clause it named moves. There is no answer being
 * kept for that to be wrong about.
 */
class WhereAClauseIsWrittenIsAskedByWhatPointsAtItTest {

    private static final String RULED = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0
            """;

    /** Builds one out of a number nothing here says anything about, so the rule is left standing and
     *  the construction is warned about — which is the body that has a place to be tempted by. */
    private static final String BUILDING = """
            module shop.cart exposing ( make )

            import shop.prices ( Amount )

            behavior make : (n: Int) -> Amount
                constructs Amount
            let make (n) = Amount(n)
            """;

    @Test
    void checkingABodyNeverAsksWhereAClauseIsWritten() {
        Compilation c = compiled();

        assertEquals(List.of(), placesRead(c, new Bodies.CheckedBehavior("shop.cart", "make")),
                "the body was judged against a rule, and asked where that rule is written");
    }

    @Test
    void norDoesCheckingTheModuleAroundIt() {
        Compilation c = compiled();

        assertEquals(List.of(), placesRead(c, new Bodies.Checked("shop.cart")),
                "the module holding that body asked where a rule is written");
    }

    @Test
    void andTheWarningAboutItDoes() {
        Compilation c = compiled();

        assertFalse(placesRead(c, new Bodies.InvariantWarnings("shop.cart")).isEmpty(),
                "nothing in this workspace asks where a clause is written, so the two above are"
                        + " held over a store that could not have answered otherwise");
    }

    /** Every question about where a clause is written that answering {@code key} read, however far
     *  down. The whole reading and not what it asked for directly: a place read through something
     *  else is a place this answer rests on. */
    private static List<Key<?>> placesRead(Compilation c, Key<?> key) {
        Db db = c.db();
        assertTrue(db.isComputed(key), "nothing asked " + key + ", so its reading is empty and"
                + " says nothing about what a check reads");
        Map<Key<?>, Boolean> seen = new LinkedHashMap<>();
        Deque<Key<?>> owed = new ArrayDeque<>();
        Set<Key<?>> places = new LinkedHashSet<>();
        owed.add(key);
        seen.put(key, true);
        while (!owed.isEmpty()) {
            for (Key<?> read : db.dependenciesOf(owed.remove())) {
                if (read instanceof Shapes.ClauseLocation) {
                    places.add(read);
                }
                if (seen.putIfAbsent(read, true) == null) {
                    owed.add(read);
                }
            }
        }
        return List.copyOf(places);
    }

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", RULED);
        byId.put("cart.sou", BUILDING);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertEquals(List.of(), c.errors(), "this workspace is supposed to compile");
        return c;
    }
}
