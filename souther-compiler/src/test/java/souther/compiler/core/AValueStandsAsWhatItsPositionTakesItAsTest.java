package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.check.EmittedDefinition;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the checker lets a value stand as a type wider than its own, the tree says so there.
 *
 * <p>Every position the checker places a value at a type it decided is one of these: the branches
 * of a fork at what they join at, the elements of a list, the two sides of {@code ++}, an argument at
 * its parameter, a field at the field's type and a spread field too, what an optional is given, what
 * a behavior answers at what it declares, and what a fold's step answers at the accumulator. At each
 * of them what stands in the slot is of the type the position takes, and where the value itself is
 * narrower it is a {@link Core.Widen} holding it — so a reader holding the two types never has to ask
 * whether the one may stand as the other.
 *
 * <p>And where the two are one type, nothing is said: a value standing as its own type is where it
 * is as it is.
 */
class AValueStandsAsWhatItsPositionTakesItAsTest {

    private static final String MODULE = """
            module demo

            data Circle = { r: Int }
            data Square = { side: Int }
            data Shape  = Circle | Square

            data Holder = { s: Shape }
            data Narrow = { s: Circle }
            data Perhaps = { s: Shape? }

            behavior root : (n: Int) -> Shape
            let root (n) = Circle { r = n }

            behavior branches : (n: Int) -> Shape
            let branches (n) = if n > 0 then Circle { r = n } else Square { side = n }

            behavior arms : (s: Shape) -> Shape
            let arms (s) = match s with
                | Circle as c -> Square { side = c.r }
                | Square as q -> Circle { r = q.side }

            behavior listed : (n: Int) -> List<Shape>
            let listed (n) = [Circle { r = n }, Square { side = n }]

            behavior appended : (n: Int) -> List<Shape>
            let appended (n) = [Circle { r = n }] ++ [Square { side = n }]

            behavior rounded : (d: Decimal) -> Decimal
            let rounded (d) = Decimal.round(2, HALF_UP, d)

            behavior held : (n: Int) -> Holder
            let held (n) = Holder { s = Circle { r = n } }

            behavior spread : (w: Narrow) -> Holder
            let spread (w) = Holder { ...w }

            behavior kept : (n: Int) -> Perhaps
            let kept (n) = Perhaps { s = Circle { r = n } }

            behavior folded : (xs: List<Int>) -> Shape
            let folded (xs) = List.fold((acc, x) -> Circle { r = x }, Square { side = 0 }, xs)

            behavior same : (n: Int) -> Int
            let same (n) = if n > 0 then 1 else 2

            let radius (s: Shape) : Int = match s with
                | Circle as c -> c.r
                | Square as q -> q.side
            partial let deep (n: Int) : Shape =
                if n > 10 then Circle { r = n } else Circle { r = radius(deep(n + 1)) }

            behavior deepest : (n: Int) -> Shape
            let deepest (n) = deep(n)

            behavior tallied : (cs: List<Circle>, k: Int) -> Int
            let tallied (cs, k) = {
                let f: (Int, Shape) -> Int =
                    if k > 0 then (acc, s) -> acc + radius(s) else (acc, s) -> acc
                List.fold(f, 0, cs)
            }
            """;

    @Test
    void whatAHelperAnswersStandsAsWhatItDeclares() {
        EmittedDefinition deep = bodies().emittedDefinitions().get("deep");
        assertNotNull(deep, "a helper that calls itself is emitted, with the body it was checked as");
        Core.Widen standing = assertInstanceOf(Core.Widen.class, deep.body(),
                "a body narrower than what its helper declares stands as what it declares");
        assertEquals("Shape", Type.show(standing.type()));
        assertEquals("Circle", Type.show(standing.value().type()));
    }

    @Test
    void aFunctionTakingMoreStandsAsOneTakingWhatTheCallHandsIt() {
        List<Core.Widen> functions = every(body("tallied"), Core.Widen.class).stream()
                .filter(each -> each.type() instanceof Type.FnOf)
                .toList();
        assertEquals(1, functions.size(), "one function stands as another here");
        Type.FnOf takes = (Type.FnOf) functions.getFirst().type();
        Type.FnOf own = (Type.FnOf) functions.getFirst().value().type();
        assertEquals("Circle", Type.show(takes.params().get(1)),
                "it stands as a step taking the element the call hands it");
        assertEquals("Shape", Type.show(own.params().get(1)),
                "while it takes the sum that element is a case of");
    }

    @Test
    void whatABehaviorAnswersStandsAsWhatItDeclares() {
        Core body = body("root");
        Core.Widen standing = assertInstanceOf(Core.Widen.class, body,
                "the construction a behavior declared to answer a sum answers stands as the sum");
        assertEquals("Shape", Type.show(standing.type()));
        assertInstanceOf(Core.Construct.class, standing.value(), "and what it holds is built");
        assertEquals("Circle", Type.show(standing.value().type()));
    }

    @Test
    void eachBranchStandsAsWhatTheBranchesJoinAt() {
        Core.If fork = only(body("branches"), Core.If.class);
        assertEachStandsAs(fork.type(), List.of(fork.then(), fork.els()), "a branch");
    }

    @Test
    void eachArmStandsAsWhatTheArmsJoinAt() {
        Core.Match match = only(body("arms"), Core.Match.class);
        assertEachStandsAs(match.type(),
                match.cases().stream().map(Core.Case::body).toList(), "an arm");
    }

    @Test
    void eachElementStandsAsWhatTheElementsJoinAt() {
        Core.ListLit list = only(body("listed"), Core.ListLit.class);
        Type element = ((Type.ListOf) list.type()).element();
        assertEachStandsAs(element, list.elements(), "an element");
    }

    @Test
    void eachSideOfAConcatenationStandsAsTheListBothJoinAt() {
        Core.Binary concatenated = only(body("appended"), Core.Binary.class);
        assertEachStandsAs(concatenated.type(),
                List.of(concatenated.left(), concatenated.right()), "a side of `++`");
    }

    @Test
    void anArgumentStandsAsTheParameterItIsHandedTo() {
        Core.Call call = only(body("rounded"), Core.Call.class);
        Core.Widen mode = assertInstanceOf(Core.Widen.class, call.args().get(1),
                "a case handed to a parameter of its sum stands as the sum");
        assertEquals("RoundingMode", Type.show(mode.type()));
        assertEquals("HALF_UP", Type.show(mode.value().type()));
    }

    @Test
    void aFieldIsGivenWhatStandsAsItsType() {
        Core.Construct built = assertInstanceOf(Core.Construct.class, body("held"),
                "the behavior answers the construction it declares it answers");
        Core.Widen given = assertInstanceOf(Core.Widen.class, built.values().get(0).value(),
                "a case given to a field of its sum stands as the sum");
        assertEquals("Shape", Type.show(given.type()));
        assertEquals("Circle", Type.show(given.value().type()));
    }

    @Test
    void andSoIsAFieldASpreadSupplies() {
        Core.Construct built = only(body("spread"), Core.Construct.class);
        Core.Widen given = assertInstanceOf(Core.Widen.class, built.values().get(0).value(),
                "a field read off a spread narrower than the field it is given to stands as it");
        assertEquals("Shape", Type.show(given.type()));
        assertInstanceOf(Core.FieldAccess.class, given.value(),
                "and what it holds is the read of the field off the value spread");
    }

    @Test
    void whatAnOptionalIsGivenStandsAsWhatItHolds() {
        Core.OptionSome some = only(body("kept"), Core.OptionSome.class);
        Core.Widen held = assertInstanceOf(Core.Widen.class, some.value(),
                "a case put in an optional of its sum stands as the sum");
        assertEquals("Shape", Type.show(held.type()));
        assertEquals("Shape", Type.show(((Type.OptionOf) some.type()).element()));
    }

    @Test
    void whatAStepAnswersStandsAsTheAccumulatorItGrows() {
        Core.Block step = only(body("folded"), Core.Block.class);
        Core.Widen answered = assertInstanceOf(Core.Widen.class, step.body(),
                "a step answering a case of the accumulator's sum answers it as the sum");
        assertEquals("Shape", Type.show(answered.type()));
        assertEquals("Shape", Type.show(((Type.FnOf) step.type()).result()),
                "and the step is of the type the call takes it at");
    }

    /** And the seed, a case of the sum the accumulator was settled at, stands as the sum. */
    @Test
    void andTheSeedStandsAsTheAccumulator() {
        Core.Call fold = null;
        for (Core.Call each : every(body("folded"), Core.Call.class)) {
            if (each.args().size() > 1) {
                fold = each;
            }
        }
        assertNotNull(fold, "the fold is a call");
        Type accumulator = ((Type.FnOf) fold.args().get(0).type()).params().get(0);
        Core seed = fold.args().get(1);
        assertEquals(accumulator, seed.type(),
                "the seed stands as the accumulator the step was read at");
        assertEquals("Square", Type.show(Core.withoutStanding(seed).type()),
                "while what it holds is the case it is");
    }

    @Test
    void whereTheTypesAreOneNothingIsSaid() {
        assertTrue(every(body("same"), Core.Widen.class).isEmpty(),
                "a value standing as its own type is where it is as it is");
    }

    @Test
    void aWidenSaysOnlyWhatDiffers() {
        Core.Widen standing = (Core.Widen) body("root");
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Widen(standing.value(), standing.value().type()),
                "a value is not widened to its own type");
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Widen(standing, standing.type()),
                "a value stands at a position once");
        assertSame(standing.value(), Core.standingAs(standing.value(), standing.value().type()),
                "standing as its own type is the value itself");
        assertEquals(standing, Core.standingAs(standing, standing.type()),
                "and standing again as what it stands as is the one standing");
    }

    @Test
    void aRewriteKeepsWhatAValueStandsAs() {
        Core.Widen standing = (Core.Widen) body("root");
        Core.Construct held = (Core.Construct) standing.value();
        Core copied = Core.mapAll(standing,
                child -> child == held ? new Core.Construct(held.typeName(), held.values(),
                        held.type(), held.pos()) : child,
                name -> name);
        Core.Widen still = assertInstanceOf(Core.Widen.class, copied,
                "a rewrite of what a Widen holds keeps it standing");
        assertEquals(standing.type(), still.type());
        assertFalse(still.value() == held, "and holds what was rewritten");
    }

    private static void assertEachStandsAs(Type position, List<Core> values, String what) {
        boolean anyWidened = false;
        for (Core value : values) {
            assertEquals(position, value.type(), what + " is of the type the position takes");
            anyWidened |= value instanceof Core.Widen;
        }
        assertTrue(anyWidened, "at least one " + what + " here is narrower than the position, so"
                + " this says something about a Widen");
    }

    private static <T extends Core> T only(Core body, Class<T> kind) {
        List<T> found = every(body, kind);
        assertEquals(1, found.size(), () -> "one " + kind.getSimpleName() + " in " + body);
        return found.getFirst();
    }

    private static <T extends Core> List<T> every(Core body, Class<T> kind) {
        List<T> out = new ArrayList<>();
        collect(body, kind, out);
        return out;
    }

    private static <T extends Core> void collect(Core e, Class<T> kind, List<T> out) {
        if (kind.isInstance(e)) {
            out.add(kind.cast(e));
        }
        Core.forEachChild(e, child -> collect(child, kind, out));
    }

    private static Core body(String behavior) {
        Core body = bodies().behaviorBodies().get(behavior);
        assertNotNull(body, "`" + behavior + "` has a body");
        return body;
    }

    private static Bodies.Elaborated checked;

    private static Bodies.Elaborated bodies() {
        if (checked != null) {
            return checked;
        }
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test was checked");
        return checked;
    }
}
