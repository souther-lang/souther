package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.core.ValueShape;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.Declared;
import souther.compiler.program.DeclaredBy;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

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

    private static CheckedProgram demoProgram() {
        return CheckedProgram.of(List.of(MODULE));
    }

    private static CheckedModule demo() {
        CheckedModule module = demoProgram().module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    /**
     * What a value of {@code name} is made of, as an output laying one out asks for it.
     *
     * <p>Of the program and with the identity, which is the whole of what a reader has to do: the
     * module that declares it is on the name, and the reader neither picks it nor is told to.
     */
    private static CheckedData layout(CheckedProgram program, TypeSymbol.AtModule name) {
        Declared declared = program.declaration(name);
        assertEquals(DeclaredBy.A_MODULE, declared.declaredBy(), name::toString);
        return declared.data();
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

    private static List<String> fieldNames(CheckedData.WithFields built) {
        return built.fields().stream().map(ValueShape.Field::name).toList();
    }

    /**
     * Every declaration the module has, and no other.
     *
     * <p>The whole set, because the whole set is what is claimed — a reader that walks this list to
     * lay out a program is told here that it has met everything. Not the order: a declaration
     * written on its own and one a sum's case list declares ({@code Plain}, {@code Express}) reach
     * the list by different routes, and nothing decided which of the two comes first. Fixing that
     * here would make how the module was read into something a reader could build on.
     */
    @Test
    void aModuleAnswersWithEveryDeclarationItHasAndNoOther() {
        CheckedModule module = demo();

        assertEquals(
                Set.of("Amount", "Common", "Wide", "Only", "Both", "First", "Middle", "Last",
                        "Left", "Right", "Reach", "Kind", "Plain", "Express"),
                Set.copyOf(names(module.data())));
        assertEquals(14, module.data().size(), "one entry per declaration");
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
                product(module, "Wide").fields().stream().map(ValueShape.Field::type).toList());
    }

    /**
     * A newtype is its own arm, made of the one field it wraps.
     *
     * <p>Both halves at once. A reader laying a value out is answered as it is for any other data
     * built field by field — the field is there, with the type it wraps — and a reader writing a
     * value is told which form was declared, which is the thing the fields do not say.
     */
    @Test
    void aNewtypeIsItsOwnArmMadeOfTheOneFieldItWraps() {
        CheckedData.Newtype amount =
                assertInstanceOf(CheckedData.Newtype.class, declared(demo(), "Amount"));

        assertEquals(Type.INT, amount.wrapped());
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
     * descent already made, with a case reached twice appearing once. This is the shape two
     * readers descending for themselves would differ at, and it is the shape neither of them would
     * have been written against.
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
     * {@link CheckedData.WithFields#positionOf}, which reads the name a construction wrote. Held
     * here because a store and a load that came to disagree would disagree silently, and this is
     * the one place both readings are visible at once.
     *
     * <p>Over both forms a construction can build. {@code Amount(n)} builds a newtype and writes
     * the one field it wraps, so a reading that asked only about products would leave a
     * construction this module writes unaccounted for.
     */
    @Test
    void everyConstructionFillsTheDeclaredFieldsInTheOrderTheyAreLaidOut() {
        CheckedProgram program = demoProgram();
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        List<Core.Construct> constructions = new ArrayList<>();
        for (Core body : bodiesOf(module)) {
            collect(body, Core.Construct.class, constructions);
        }

        assertEquals(2, constructions.size(), () -> "the constructions this module writes: "
                + constructions.stream().map(each -> each.typeName().name()).toList());
        for (Core.Construct construction : constructions) {
            CheckedData.WithFields built = assertInstanceOf(CheckedData.WithFields.class,
                    layout(program, construction.typeName()), construction.typeName()::toString);
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
     * place. What can be read from is a data built field by field — either form of one, since
     * {@code x.value} reads a newtype the way {@code w.extra} reads a product — and a sum every
     * case of which carries the field, which is answered by the leaves the sum already descended
     * to.
     */
    @Test
    void everyFieldReadNamesAFieldOfWhatItReadsFrom() {
        CheckedProgram program = demoProgram();
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        List<Core.FieldAccess> reads = new ArrayList<>();
        for (Core body : bodiesOf(module)) {
            collect(body, Core.FieldAccess.class, reads);
        }

        assertEquals(2, reads.size(), () -> "the field reads this module writes: "
                + reads.stream().map(Core.FieldAccess::field).toList());
        int offSums = 0;
        int offFields = 0;
        List<Core.FieldAccess> unaccounted = new ArrayList<>();
        for (Core.FieldAccess read : reads) {
            if (!(read.target().type() instanceof Type.Ref(TypeSymbol.AtModule named))) {
                unaccounted.add(read);
                continue;
            }
            switch (layout(program, named)) {
                // Answering at all is the assertion: a name that is no field of it is refused.
                case CheckedData.WithFields built -> {
                    offFields++;
                    built.positionOf(read.field());
                }
                case CheckedData.Sum sum -> {
                    offSums++;
                    assertEquals(List.of("Wide", "Only"),
                            sum.cases().stream().map(TypeSymbol::name).toList(),
                            () -> "the cases " + named + " is read across");
                    for (TypeSymbol leaf : sum.cases()) {
                        CheckedData.WithFields carrying = assertInstanceOf(
                                CheckedData.WithFields.class,
                                layout(program, assertInstanceOf(TypeSymbol.AtModule.class, leaf)),
                                leaf::toString);
                        carrying.positionOf(read.field());
                    }
                }
                case CheckedData.Unit _ ->
                        throw new AssertionError("a unit has no field to read: " + named);
            }
        }
        assertEquals(1, offSums, "the read off a sum is the one this module writes");
        assertEquals(1, offFields,
                "the read off a data built field by field is the one this module writes");
        // Every read is accounted for, so a read of a shape this does not know how to place cannot
        // pass by being skipped. The two arms above are what the language admits reading a field
        // off; a read that arrived at neither would be the finding, and going quiet about it is
        // what would hide one.
        assertEquals(List.of(), unaccounted.stream().map(Core.FieldAccess::field).toList(),
                "a field read of a shape neither arm answers for");
    }

    /** A second module, so that a name declared somewhere other than {@code demo} is one this test
     *  can hold rather than one it has to imagine. */
    private static final String OTHER = """
            module other

            data Elsewhere = { n: Int }
            """;

    /**
     * A declaration is reached by its identity, and not through whichever module the reader holds.
     *
     * <p>Which module declares a name is on the name, so a reader asked to pick the owner first is
     * being asked to restate what it is already holding — and where the declaration is the
     * language's own there is no module of the compilation to pick. Enumerating is still a module's
     * question, and a module this compile did not check is still nothing.
     */
    @Test
    void aDeclarationIsReachedByItsIdentityAndNotThroughAModule() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, OTHER));
        CheckedModule other = program.module("other");
        assertNotNull(other);
        TypeSymbol.AtModule elsewhere = declared(other, "Elsewhere").name();

        assertNull(program.module("nowhere"), "this compile checked no module of that name");
        assertSame(declared(other, "Elsewhere"), layout(program, elsewhere),
                "the program answers for it, whichever module the reader happened to be holding");
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
