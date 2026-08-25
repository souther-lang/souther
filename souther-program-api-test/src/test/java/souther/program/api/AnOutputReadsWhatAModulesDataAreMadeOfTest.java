package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output that is not this compiler can learn about a module's declared data.
 *
 * <p>A backend lays a value out, loads a field out of one, and decides which case a running value
 * is. None of the three is readable from a {@link Type.Ref}, which is a name; all three are
 * decisions this compiler made. What is held here is that they cross whole — that a reader is given
 * the answer rather than the materials to work it out a second time.
 */
class AnOutputReadsWhatAModulesDataAreMadeOfTest {

    /**
     * A module written to be read rather than to be run.
     *
     * <p>{@code Wide} takes {@code Common} in, so its fields are laid out with what the include
     * brought in first. {@code Both} is a sum over two cases that each take {@code Common} in, and
     * what every case carries is a property of the sum — which is what lets {@code idOf} read
     * {@code id} off the sum itself. {@code Reach} is a sum of sums, and {@code Left} and
     * {@code Right} both reach {@code Middle}, so a descent that counted paths would count it
     * twice. {@code Amount} is a newtype.
     */
    private static final String MODULE = """
            module demo

            data Amount = Int

            data Common = { id: Int, tag: String }

            data Wide  = { ...Common, extra: Int }
            data Only  = { ...Common }

            data Both = Wide | Only

            data First  = { ...Common }
            data Middle = { ...Common }
            data Last   = { ...Common }

            data Left  = First | Middle
            data Right = Middle | Last
            data Reach = Left | Right

            data Kind = Plain | Express

            // Reads a field of a product this module never constructs, which is the reading a
            // backend emits a load for.
            behavior extraOf : (w: Wide) -> Int

            let extraOf (w) = w.extra

            // Reads a field off the sum, which every case carries because every case takes
            // `Common` in.
            behavior idOf : (b: Both) -> Int

            let idOf (b) = b.id

            behavior wrap : (n: Int) -> Amount constructs Amount

            let wrap (n) = Amount(n)

            behavior widen : (n: Int) -> Wide constructs Wide

            // Written in an order the declaration does not lay out, so that a snapshot agreeing
            // with the construction is agreeing about the checked program rather than about how
            // this literal happens to be typed out.
            let widen (n) = Wide { extra = n, id = n, tag = "t" }
            """;

    private static CheckedModule demo() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    private static CheckedData declared(CheckedModule module, String name) {
        for (CheckedData each : module.data()) {
            if (each.name().name().equals(name)) {
                return each;
            }
        }
        throw new AssertionError(name + " is not among " + names(module.data()));
    }

    private static CheckedData.Product product(CheckedModule module, String name) {
        return assertInstanceOf(CheckedData.Product.class, declared(module, name), name);
    }

    private static List<String> names(List<CheckedData> data) {
        return data.stream().map(each -> each.name().name()).toList();
    }

    private static List<String> fieldNames(CheckedData.Product product) {
        return product.fields().stream().map(CheckedData.Field::name).toList();
    }

    @Test
    void aModuleAnswersWithWhatItDeclares() {
        CheckedModule module = demo();

        assertTrue(names(module.data()).containsAll(
                        List.of("Amount", "Common", "Wide", "Both", "Reach", "Kind")),
                () -> "declared " + names(module.data()));
    }

    /**
     * The include is already flattened, and what it brought in comes first.
     *
     * <p>The order is the layout. A reader given the includes instead would work the flattening out
     * for itself, and this compiler and that reader would be two places deciding where a field
     * lies.
     */
    @Test
    void aProductAnswersEveryFieldItHoldsWithAnIncludesFieldsFirst() {
        CheckedModule module = demo();

        assertEquals(List.of("id", "tag", "extra"), fieldNames(product(module, "Wide")));
        assertEquals(List.of("id", "tag"), fieldNames(product(module, "Common")));
        assertEquals(List.of(Type.INT, Type.STRING, Type.INT),
                product(module, "Wide").fields().stream().map(CheckedData.Field::type).toList());
    }

    /**
     * A newtype is the one-field product it is.
     *
     * <p>Held to deliberately. What differs about a newtype is how it is written outside the
     * program, which is no part of what a value is made of, so a reader laying one out has nothing
     * to tell it from any other single-field product.
     */
    @Test
    void aNewtypeIsAProductOfTheOneFieldItWraps() {
        CheckedData.Product amount = product(demo(), "Amount");

        assertEquals(List.of("value"), fieldNames(amount));
        assertEquals(Type.INT, amount.fields().get(0).type());
    }

    /** A unit is its own arm, and not a product that happens to have no fields. */
    @Test
    void aUnitIsItsOwnArm() {
        assertInstanceOf(CheckedData.Unit.class, declared(demo(), "Plain"));
    }

    /**
     * A sum answers what a value of it can be, which is not the cases it lists.
     *
     * <p>{@code Reach} lists two sums, and both of them reach {@code Middle}. What crosses is the
     * descent this compiler already makes, with a case reached twice appearing once — the answer
     * four readers inside the compiler used to work out for themselves and disagreed about at
     * exactly this shape.
     */
    @Test
    void aSumAnswersTheLeafCasesAValueOfItCanBe() {
        CheckedModule module = demo();

        CheckedData.Sum reach = assertInstanceOf(CheckedData.Sum.class, declared(module, "Reach"));

        assertEquals(List.of("First", "Middle", "Last"),
                reach.cases().stream().map(TypeSymbol::name).toList());
        assertEquals(3, reach.cases().size(), () -> "a case reached twice is one case: "
                + reach.cases());
    }

    /**
     * A case belongs to two sums as one identity standing at two positions.
     *
     * <p>Which is why a position here is not a tag. A reader that made one into a discriminator
     * would have given {@code Middle} two of them, and the values a program passes between the two
     * sums are the same values.
     */
    @Test
    void aCaseOfTwoSumsIsOneIdentityAtTwoPositions() {
        CheckedModule module = demo();

        List<TypeSymbol> left = assertInstanceOf(CheckedData.Sum.class,
                declared(module, "Left")).cases();
        List<TypeSymbol> right = assertInstanceOf(CheckedData.Sum.class,
                declared(module, "Right")).cases();

        assertEquals(1, left.indexOf(middleOf(left)));
        assertEquals(0, right.indexOf(middleOf(right)));
        assertEquals(middleOf(left), middleOf(right), "one declaration, one identity");
    }

    private static TypeSymbol middleOf(List<TypeSymbol> cases) {
        return cases.stream().filter(each -> each.name().equals("Middle")).findFirst()
                .orElseThrow(() -> new AssertionError("no Middle among " + cases));
    }

    /**
     * A field is reached by its name, whatever order the names are asked in.
     *
     * <p>The one derivation of a position from a name. Asked out of order because a reader walking
     * a construction asks in the order the construction evaluates, and a reader emitting a load
     * asks for one field alone — neither is walking the layout.
     */
    @Test
    void aFieldIsFoundByItsNameWhateverOrderItIsAskedIn() {
        CheckedData.Product wide = product(demo(), "Wide");

        assertEquals(2, wide.positionOf("extra"));
        assertEquals(0, wide.positionOf("id"));
        assertEquals(1, wide.positionOf("tag"));
    }

    /** A name that is no field of it is refused rather than answered with a position that is not
     *  one. */
    @Test
    void aNameThatIsNoFieldOfItIsRefused() {
        CheckedData.Product wide = product(demo(), "Wide");

        NoSuchElementException refused =
                assertThrows(NoSuchElementException.class, () -> wide.positionOf("absent"));

        assertTrue(refused.getMessage().contains("absent"), refused::getMessage);
    }

    /**
     * Every construction fills the declared fields, in the order they are laid out.
     *
     * <p>A property of the checked program and not how a reader places a field — that is
     * {@link CheckedData.Product#positionOf}, which reads the name a construction wrote. Held here
     * because a store and a load that came to disagree would disagree silently, and this is the one
     * place both readings are visible at once.
     */
    @Test
    void everyConstructionFillsTheDeclaredFieldsInTheOrderTheyAreLaidOut() {
        CheckedModule module = demo();
        List<Core.Construct> constructions = new ArrayList<>();
        for (Core body : bodiesOf(module)) {
            collect(body, Core.Construct.class, constructions);
        }

        assertTrue(constructions.size() >= 2, () -> "found " + constructions.size());
        for (Core.Construct construction : constructions) {
            CheckedData.Product built = assertInstanceOf(CheckedData.Product.class,
                    module.data(construction.typeName()), construction.typeName()::toString);
            assertEquals(fieldNames(built),
                    construction.values().stream().map(Core.FieldValue::field).toList(),
                    () -> "what `" + construction.typeName() + "` is built with");
        }
    }

    /**
     * Every field read names a field of what it reads from.
     *
     * <p>The other half of the same reading, and the half a construction cannot stand in for: a
     * module may read a field of a product it never builds, and that read is what a backend has to
     * place. Two shapes can be read from — a product, and a sum every case of which carries the
     * field — and the second is answered by the leaves the sum already descended to.
     */
    @Test
    void everyFieldReadNamesAFieldOfWhatItReadsFrom() {
        CheckedModule module = demo();
        List<Core.FieldAccess> reads = new ArrayList<>();
        for (Core body : bodiesOf(module)) {
            collect(body, Core.FieldAccess.class, reads);
        }

        assertTrue(reads.size() >= 2, () -> "found " + reads.size());
        int offSums = 0;
        int offProducts = 0;
        for (Core.FieldAccess read : reads) {
            if (!(read.target().type() instanceof Type.Ref(TypeSymbol.AtModule named))) {
                continue;
            }
            switch (module.data(named)) {
                // Answering at all is the assertion: a name that is no field of it is refused.
                case CheckedData.Product product -> {
                    offProducts++;
                    product.positionOf(read.field());
                }
                case CheckedData.Sum sum -> {
                    offSums++;
                    assertTrue(!sum.cases().isEmpty(), () -> "no cases on " + named);
                    for (TypeSymbol leaf : sum.cases()) {
                        CheckedData.Product carrying = assertInstanceOf(CheckedData.Product.class,
                                module.data(assertInstanceOf(TypeSymbol.AtModule.class, leaf)),
                                leaf::toString);
                        carrying.positionOf(read.field());
                    }
                }
                case CheckedData.Unit _ ->
                        throw new AssertionError("a unit has no field to read: " + named);
                case null -> throw new AssertionError(named + " is declared by no module here");
            }
        }
        assertEquals(1, offSums, "the read off a sum is the one this module writes");
        assertTrue(offProducts >= 1, () -> "no read off a product among " + reads.size());
    }

    /**
     * Which module a name belongs to is asked before what the name is, and the two absences are
     * separate answers.
     */
    @Test
    void aModuleThisCompileDidNotCheckAndANameItDoesNotDeclareAreTwoAnswers() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertNull(program.module("elsewhere"), "this compile checked no such module");
        CheckedModule module = program.module("demo");
        assertNotNull(module);
        assertSame(declared(module, "Wide"), module.data(declared(module, "Wide").name()));
    }

    /** Every body this module holds: a behavior written here, and a helper it emits. */
    private static List<Core> bodiesOf(CheckedModule module) {
        List<Core> bodies = new ArrayList<>();
        for (CheckedBehavior behavior : module.behaviors()) {
            if (behavior.implementation() instanceof CheckedImplementation.Body written) {
                bodies.add(written.body());
            }
        }
        for (CheckedHelper helper : module.helpers()) {
            bodies.add(helper.body());
        }
        return bodies;
    }

    /** Every node of {@code of} in the tree under {@code from}, itself included. */
    private static <T extends Core> void collect(Core from, Class<T> of, List<T> out) {
        if (of.isInstance(from)) {
            out.add(of.cast(from));
        }
        Core.forEachChild(from, child -> collect(child, of, out));
    }
}
