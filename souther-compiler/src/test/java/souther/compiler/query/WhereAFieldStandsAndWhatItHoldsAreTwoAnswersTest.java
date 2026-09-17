package souther.compiler.query;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a declaration's fields stand and what each of them holds are two questions, and an edit
 * that changes only the first reaches its readers and leaves the readers of the second alone.
 *
 * <p>The edit is two spreads written the other way round, which is what changes the layout and
 * nothing else. Not every edit that moves a field is: a declaration's own fields moved among
 * themselves are numbered the other way round, so which binding each of them is moves too. What is
 * held below is the edit that separates the three answers, and there is only one kind of it.
 *
 * <p>Both halves here, on one edit. Held apart they are both true of a compiler that answers only
 * one of them: a store that never noticed the edit passes the half about what the fields hold, and
 * one that folded the order back in passes the half about where they stand. What neither passes is
 * the pair.
 *
 * <p>And the pair is what a value of the type is made of. A constructor takes the fields in the
 * order they are laid out, so a module that builds a value of a declaration another module wrote
 * has to be worked out again when that declaration's fields move — while one that only reads a
 * field by name does not. The last test says the first half of that as a reader sees it: the same
 * edit made to a workspace being kept, and made to one compiled from nothing, come out the same
 * bytes.
 */
class WhereAFieldStandsAndWhatItHoldsAreTwoAnswersTest {

    private static final TypeKey PAIR = new TypeKey("shop.prices", "Pair");

    /** Two spreads, so that moving them moves no field among the ones its own declaration wrote. */
    private static final String PRICES = """
            module shop.prices exposing ( Pair )

            data A = { qty: Int }

            data B = { note: String }

            data Pair = { ...A, ...B }
            """;

    /** The same declarations with the two spreads written the other way round. */
    private static final String PRICES_SWAPPED = """
            module shop.prices exposing ( Pair )

            data A = { qty: Int }

            data B = { note: String }

            data Pair = { ...B, ...A }
            """;

    /** The same fields written on the declaration itself, and the same two written the other way
     *  round — the other kind of edit that moves a field. */
    private static final String PRICES_OWN = """
            module shop.prices exposing ( Pair )

            data Pair = { qty: Int, note: String }
            """;

    private static final String PRICES_OWN_SWAPPED = """
            module shop.prices exposing ( Pair )

            data Pair = { note: String, qty: Int }
            """;

    /** Builds a value of the declaration above, so an edit to where its fields stand reaches here. */
    private static final String CART = """
            module shop.cart exposing ( make )

            import shop.prices ( Pair )

            behavior make : (n: Int) -> Pair
                constructs Pair
            let make (n) = Pair { qty = n, note = "x" }
            """;

    /**
     * The edit moves where the fields stand and moves nothing about what they hold or which binding
     * each of them is.
     */
    @Test
    void writingTheSpreadsInAnotherOrderMovesWhereTheFieldsStandAndNothingElse() {
        Compilation c = compiling(PRICES);
        Map<String, Type> held = fields(c);
        Map<String, BindingId> bound = bindings(c);
        List<String> stood = layout(c);
        assertEquals(List.of("qty", "note"), stood, "what a spread brings in stands where it is"
                + " spread, and the declaration's own after");

        edit(c, PRICES_SWAPPED);

        assertEquals(List.of("note", "qty"), layout(c),
                "the spreads are written the other way round, so the fields stand the other way"
                        + " round");
        assertNotEquals(stood, layout(c), "which is a change to this answer");
        assertEquals(held, fields(c),
                "and no change to what each of them holds, which is what that answer is about");
        assertEquals(bound, bindings(c),
                "nor to which binding each of them is: a field brought in keeps the number the"
                        + " declaration that wrote it gave it, and neither of those moved");
    }

    /**
     * The other kind of edit that moves a field: a declaration's own two written the other way
     * round. Where they stand moves, and so does which binding each of them is.
     *
     * <p>Held beside the one above because together they say what each answer is about. A binding
     * is which field of its owner it is, so a field moved among its siblings is numbered the other
     * way round — which is a fact about the numbering and not about the layout, and the two answers
     * move here for two reasons rather than one. What still does not move is what the fields hold.
     */
    @Test
    void movingADeclarationsOwnFieldsMovesWhereTheyStandAndWhichBindingEachIs() {
        Compilation c = compiling(PRICES_OWN);
        Map<String, Type> held = fields(c);
        Map<String, BindingId> bound = bindings(c);
        assertEquals(List.of("qty", "note"), layout(c));

        edit(c, PRICES_OWN_SWAPPED);

        assertEquals(List.of("note", "qty"), layout(c), "the fields stand the other way round");
        assertNotEquals(bound, bindings(c),
                "and each is numbered the other way round, which is what a binding is");
        assertEquals(held, fields(c),
                "what they hold is what neither kind of edit moves");
    }

    /**
     * A reader that builds a value of the declaration is worked out again, which is said of the
     * reader rather than of the answer: it asks where the fields stand, so the edit reaches it.
     */
    @Test
    void whatBuildsAValueOfTheDeclarationAsksWhereItsFieldsStand() {
        Compilation c = compiling(PRICES, CART);
        c.db().ask(new Bodies.CheckedBehavior("shop.cart", "make"));

        assertTrue(c.db().dependenciesOf(new Bodies.CheckedBehavior("shop.cart", "make"))
                        .contains(new Shapes.FieldLayoutOf(PAIR)),
                "the check that lines a construction up against the declaration reads where its"
                        + " fields stand: " + c.db()
                        .dependenciesOf(new Bodies.CheckedBehavior("shop.cart", "make")));
    }

    /**
     * And the bytes it comes to are the bytes a compile from nothing comes to.
     *
     * <p>The one thing a reader of any of this can be held to. An answer kept across an edit is
     * kept because nothing that read it could tell the difference, and this is what tells: the
     * module that wrote the declaration lays its fields out the new way, and the module that builds
     * one hands its values over in that same new order.
     */
    @Test
    void theModuleThatBuildsOneComesOutAsThoughItHadBeenCompiledFromNothing() {
        Compilation kept = compiling(PRICES, CART);
        edit(kept, PRICES_SWAPPED, CART);

        Compilation fresh = compiling(PRICES_SWAPPED, CART);

        assertEquals(classes(fresh, "shop.prices"), classes(kept, "shop.prices"),
                "the declaring module, which is the control: it is edited and is worked out again"
                        + " whatever else holds");
        assertEquals(classes(fresh, "shop.cart"), classes(kept, "shop.cart"),
                "and the module that builds a value of it, which is the one an answer that did not"
                        + " move would have left saying what it said");
    }

    private static List<String> layout(Compilation c) {
        Answer<List<String>> answer = c.db().ask(new Shapes.FieldLayoutOf(PAIR));
        return answer.present() ? answer.value() : List.of();
    }

    private static Map<String, Type> fields(Compilation c) {
        Answer<Map<String, Type>> answer = c.db().ask(new Shapes.EffectiveFieldTypesOf(PAIR));
        return answer.present() ? answer.value() : Map.of();
    }

    private static Map<String, BindingId> bindings(Compilation c) {
        Answer<Map<String, BindingId>> answer = c.db().ask(new Shapes.FieldBindingsOf(PAIR));
        return answer.present() ? answer.value() : Map.of();
    }

    private static Map<String, ClassFileImage> classes(Compilation c, String module) {
        Answer<Map<String, ClassFileImage>> answer = c.db().ask(new Output.Classes(module));
        return answer.present() ? answer.value() : Map.of();
    }

    private static Compilation compiling(String... sources) {
        Compilation c = Compilation.ofDocuments(workspace(sources), Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                "the workspace compiles to begin with: " + c.db().allReports());
        return c;
    }

    private static void edit(Compilation c, String... sources) {
        c.update(workspace(sources), Set.of());
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                "the edited workspace compiles: " + c.db().allReports());
    }

    private static Map<String, String> workspace(String... sources) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", sources[0]);
        if (sources.length > 1) {
            byId.put("cart.sou", sources[1]);
        }
        return byId;
    }
}
