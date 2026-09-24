package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A {@code let} says in Core what type its name is in force at.
 *
 * <p>The checker enters a binder into the environment at a type of its own deciding, and that type
 * is not always the value's own. A written annotation may be a sum the value is one case of, and the
 * bindings an expansion wraps its body in hold each argument at the declared sum parameter. What the
 * body was read with is then wider than what the value was worked out as, and the value stands as
 * that wider type where it is bound: a reader of the tree reads both, and neither from the other.
 *
 * <p>Every model here hands a {@code Closed} to a binding the checker holds at {@code Deal}. One of
 * them never reads the binding, so the answer cannot be the type of some read of it: there is none.
 */
class ALetsBinderCarriesTheTypeTheBodyWasReadAtTest {

    private static final String MODULE = """
            module demo

            data Open   = { id: String }
            data Closed = { id: String }
            data Deal   = Open | Closed

            let itself (d: Deal) = d
            let ignored (d: Deal) = 1
            let counting (d: Deal) = (n) -> n

            behavior annotated : (c: Closed) -> Deal
            let annotated (c) = {
                let d: Deal = c
                d
            }

            behavior expanded : (c: Closed) -> Deal
            let expanded (c) = itself(c)

            behavior unread : (c: Closed) -> Int
            let unread (c) = ignored(c)

            behavior inAFunction : (c: Closed) -> Int
            let inAFunction (c) = {
                let f: (Int) -> Int = counting(c)
                f(1)
            }
            """;

    @Test
    void aWrittenAnnotationIsTheTypeTheNameIsInForceAt() {
        heldAtTheSum("annotated", true);
    }

    @Test
    void anExpansionBindsItsArgumentAtTheParameterItWasDeclaredAt() {
        heldAtTheSum("expanded", true);
    }

    @Test
    void andSoWhereTheBodyNeverReadsIt() {
        heldAtTheSum("unread", false);
    }

    @Test
    void andWhereWhatIsExpandedIsAFunction() {
        heldAtTheSum("inAFunction", false);
    }

    /** The one binding in {@code behavior}'s body the {@code Closed} parameter is handed to is in
     *  force at {@code Deal}, and each read of it is typed at what it is in force at. */
    private static void heldAtTheSum(String behavior, boolean read) {
        Core body = bodies().behaviorBodies().get(behavior);
        assertNotNull(body, "`" + behavior + "` has a body");
        List<Core.LetIn> bindings = new ArrayList<>();
        collect(body, Core.LetIn.class, bindings);
        List<Core.LetIn> handed = bindings.stream()
                .filter(li -> Type.show(Core.withoutStanding(li.value()).type()).equals("Closed"))
                .toList();
        assertEquals(1, handed.size(), "`" + behavior + "` binds the `Closed` it is given once");
        Core.LetIn let = handed.getFirst();

        assertEquals("Deal", Type.show(let.bindType()),
                "the binding is in force at `Deal` while its value is a `Closed`");
        assertInstanceOf(Core.Widen.class, let.value(),
                "and the value says it stands there as what the binding is in force at");
        assertEquals(let.bindType(), let.value().type(),
                "which is the type the binding is in force at");
        List<Core.Read> reads = readsOf(let.body(), let.binder().binding());
        assertEquals(read, !reads.isEmpty(),
                read ? "the body reads the binding" : "nothing reads the binding");
        for (Core.Read r : reads) {
            assertEquals(let.bindType(), r.type(), "a read is typed at what the binding holds");
        }
    }

    private static List<Core.Read> readsOf(Core body, BindingId binding) {
        List<Core.Read> reads = new ArrayList<>();
        collect(body, Core.Read.class, reads);
        return reads.stream().filter(r -> r.binding().equals(binding)).toList();
    }

    private static <T extends Core> void collect(Core e, Class<T> kind, List<T> out) {
        if (kind.isInstance(e)) {
            out.add(kind.cast(e));
        }
        Core.forEachChild(e, child -> collect(child, kind, out));
    }

    private static Bodies.Elaborated bodies() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test was checked");
        assertFalse(checked.behaviorBodies().isEmpty(), "and its behaviors have bodies");
        return checked;
    }
}
