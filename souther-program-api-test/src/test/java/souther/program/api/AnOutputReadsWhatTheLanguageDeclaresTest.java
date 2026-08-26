package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.compiler.core.ValueShape;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.Declared;
import souther.compiler.program.DeclaredBy;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a data an output holds a value of is made of, asked with the identity and answered whoever
 * declared it.
 *
 * <p>A body that writes {@code HALF_UP} carries a value typed against a declaration no module of
 * the compilation made. Reached through the module that declares it, there was nothing to reach: the
 * standard library's modules are not modules of a compilation, and an output was left holding a
 * value it could not lay out. What is held here is that the question is asked of the program with
 * the identity, and that a declaration the language gives is read exactly as a module's own is.
 *
 * <p>And that the two absences that are not one another stay apart. A module read off the path
 * declares data of its own, and what a value of one is made of was settled by the compile that
 * built it — so this program says where it is rather than that it has none. A name nothing declares
 * is neither, and is refused.
 */
class AnOutputReadsWhatTheLanguageDeclaresTest {

    /** Writes a value of a data the language declares, and nothing else out of the ordinary. */
    private static final String ROUNDS = """
            module money

            behavior rounded : (d: Decimal) -> Decimal

            let rounded (d) = Decimal.round(2, HALF_UP, d)
            """;

    private static final TypeSymbol.AtModule ROUNDING_MODE =
            TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"));

    private static final TypeSymbol.AtModule HALF_UP =
            TypeSymbols.declared(new TypeKey("souther.decimal", "HALF_UP"));

    /**
     * The sum the language declares is read as any other sum is: its cases, in the order it states
     * them.
     *
     * <p>Which is the whole of what a match over one needs, and none of it was reachable while the
     * only way to a declaration was through a module of the compilation.
     */
    @Test
    void aSumTheLanguageDeclaresIsReadAsAnyOtherSumIs() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));

        Declared.Available available = assertInstanceOf(Declared.Available.class,
                program.declaration(ROUNDING_MODE));
        assertEquals(DeclaredBy.THE_LANGUAGE, available.declaredBy(),
                "no module of a compilation declares it");
        CheckedData.Sum sum = assertInstanceOf(CheckedData.Sum.class, available.data());
        assertEquals(
                List.of("HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN", "CEILING", "FLOOR"),
                sum.cases().stream().map(TypeSymbol::name).toList(),
                "the cases a value of it can be");
    }

    /** And a case of it is the unit data it is, which is what the value a body writes stands for. */
    @Test
    void aCaseOfItIsTheUnitDataItIs() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));

        Declared.Available available = assertInstanceOf(Declared.Available.class,
                program.declaration(HALF_UP));
        assertEquals(DeclaredBy.THE_LANGUAGE, available.declaredBy());
        assertEquals(HALF_UP, assertInstanceOf(CheckedData.Unit.class, available.data()).name());
    }

    /**
     * And the body really does write one, so the reading above is of something a reader meets.
     *
     * <p>A test that only asked the program about an identity it spelled out itself would hold for a
     * declaration no program could name.
     */
    @Test
    void andABodyWritesAValueOfIt() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));
        CheckedModule module = program.module("money");
        assertNotNull(module);

        List<Core.UnitValue> written = new ArrayList<>();
        for (Core body : bodiesOf(module)) {
            collect(body, Core.UnitValue.class, written);
        }

        assertEquals(List.of(HALF_UP), written.stream().map(Core.UnitValue::data).toList(),
                "the unit values this module writes");
    }

    /**
     * Every identity a checked program reaches is one this program answers for.
     *
     * <p>The wider of the two holdings: an identity in a body was resolved by this compile, so
     * something knows what declares it, and a program that refused one would be handing an output a
     * name with nothing behind it. Whether the declaration is here or in the compile that built a
     * dependency is the next question and not this one.
     */
    @Test
    void everyIdentityAProgramReachesIsOneItAnswersFor() {
        Map<String, byte[]> classes = Compiler.compile(PUBLISHED);
        // Both programs, because the two arms are what this is about: one reaches a declaration the
        // language gives and the other one a dependency made, and a walk over either alone would
        // hold while the other went unanswered.
        CheckedProgram language = CheckedProgram.of(List.of(ROUNDS));
        CheckedProgram dependency =
                CheckedProgram.of(List.of(IMPORTS), (ModulePath) classes::get);

        // What each of them reaches, said out loud. A walk that quietly reached nothing would hold
        // here exactly as one that reached everything, and the second of these is a name this
        // compile did not check.
        assertEquals(List.of(HALF_UP), List.copyOf(everyIdentityIn(language)));
        assertEquals(List.of("app.bills.Receipt", "lib.money.Amount"),
                everyIdentityIn(dependency).stream().map(TypeSymbol.AtModule::toString).toList());

        for (CheckedProgram program : List.of(language, dependency)) {
            for (TypeSymbol.AtModule named : everyIdentityIn(program)) {
                program.declaration(named);   // answering at all is the assertion
            }
        }
    }

    /**
     * And where a value of one is being laid out, the declaration is here.
     *
     * <p>The narrower holding, and the one an output emits by. These are the places a backend has to
     * know what a value is made of — what a construction fills, what a unit value stands for, what a
     * field is read off, and which cases an arm selects — and a declaration that was somewhere else
     * would leave it with nothing to emit.
     */
    @Test
    void andWhereAValueIsLaidOutTheDeclarationIsHere() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));
        Set<TypeSymbol.AtModule> laidOut = everyIdentityLaidOutIn(program);

        assertFalse(laidOut.isEmpty(), "this module lays values out");
        for (TypeSymbol.AtModule named : laidOut) {
            assertInstanceOf(Declared.Available.class, program.declaration(named),
                    named::toString);
        }
    }

    /** Published by another project, and on the path rather than among the sources. */
    private static final String PUBLISHED = """
            module lib.money exposing ( Amount )

            data Amount = Int
            """;

    private static final String IMPORTS = """
            module app.bills
            import lib.money ( Amount )

            data Receipt = { total: Amount }

            behavior bill : (a: Amount) -> Receipt constructs Receipt

            let bill (a) = Receipt { total = a }
            """;

    /**
     * A declaration a module off the path makes is said to be there, and not said to be missing.
     *
     * <p>What a value of it is made of was decided when that module was compiled and is in that
     * compile's own snapshot. Answered because this compile read the module and found the name among
     * what it declares — so a declaration arriving some fourth way would fall through to being
     * refused rather than be taken for one of these.
     */
    @Test
    void aDeclarationOffThePathIsSaidToBeThere() {
        Map<String, byte[]> classes = Compiler.compile(PUBLISHED);
        ModulePath path = classes::get;
        CheckedProgram program = CheckedProgram.of(List.of(IMPORTS), path);
        CheckedModule module = program.module("app.bills");
        assertNotNull(module);

        TypeSymbol.AtModule amount = assertInstanceOf(TypeSymbol.AtModule.class,
                assertInstanceOf(Type.Ref.class, fieldOf(module, "Receipt", "total").type()).name());
        assertEquals("lib.money", amount.module(), "the field's type is the dependency's data");
        assertInstanceOf(Declared.OnThePath.class, program.declaration(amount));
    }

    /**
     * And a name nothing declares is refused rather than taken for one of those.
     *
     * <p>An identity exists because a declaration world said one is at an address, so a reader that
     * assembled one out of two strings is asking about something that is not a declaration. Answered
     * with the arm for a module off the path, the reader would be told to go and find a snapshot
     * that does not exist — which is the mistake it made, handed back as a state of the program.
     */
    @Test
    void andANameNothingDeclaresIsRefused() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));

        assertThrows(IllegalArgumentException.class, () -> program.declaration(
                TypeSymbols.declared(new TypeKey("no.such.module", "Missing"))),
                "no module of this compile, no module off its path, and not the language's");
        assertThrows(IllegalArgumentException.class, () -> program.declaration(
                TypeSymbols.declared(new TypeKey("souther.decimal", "Missing"))),
                "the reserved namespace is not a place a reader may name a declaration into");
    }

    /**
     * What the language declares is enumerable, so an output that has to materialise them is not
     * left walking the bodies it happened to be given.
     *
     * <p>A walk answers about the declarations something in the program names. A language
     * declaration nothing in this program writes is one such an output would never emit, and the
     * program would run into it the first time a value of it arrived from somewhere else.
     */
    @Test
    void whatTheLanguageDeclaresIsEnumerable() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));

        List<CheckedData> language = program.languageDeclarations();

        assertEquals(
                List.of("RoundingMode", "HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN",
                        "CEILING", "FLOOR"),
                language.stream().map(each -> each.name().name()).toList());
        for (CheckedData declared : language) {
            assertEquals(new Declared.Available(declared, DeclaredBy.THE_LANGUAGE),
                    program.declaration(declared.name()),
                    "the list and the lookup are one index read two ways");
        }
    }

    /** The field called {@code field} of the module's data called {@code data}. */
    private static ValueShape.Field fieldOf(CheckedModule module, String data, String field) {
        for (CheckedData declared : module.data()) {
            if (declared.name().name().equals(data)) {
                for (ValueShape.Field each : assertInstanceOf(CheckedData.Product.class, declared)
                        .fields()) {
                    if (each.name().equals(field)) {
                        return each;
                    }
                }
            }
        }
        throw new AssertionError(data + "." + field + " is not declared by " + module.name());
    }

    /**
     * Every identity this program reaches: what its declarations are made of, what its behaviors
     * take and answer, and the type of every node of every body.
     *
     * <p>Every node and not the nodes a value is laid out at. What is being held is that nothing a
     * reader can arrive at is a name the program will not answer for, so a walk that visited the
     * places the answer is already known to be needed would be holding for the reader it was
     * written from.
     */
    private static Set<TypeSymbol.AtModule> everyIdentityIn(CheckedProgram program) {
        Set<TypeSymbol.AtModule> named = new LinkedHashSet<>(everyIdentityLaidOutIn(program));
        for (CheckedModule module : program.modules()) {
            for (CheckedData declared : module.data()) {
                named.add(declared.name());
                switch (declared) {
                    case CheckedData.Product product -> {
                        for (ValueShape.Field field : product.fields()) {
                            namesIn(field.type(), named);
                        }
                    }
                    case CheckedData.Sum sum -> {
                        for (TypeSymbol each : sum.cases()) {
                            namesIn(each, named);
                        }
                    }
                    case CheckedData.Unit _ -> { }
                }
            }
            for (CheckedBehavior behavior : module.behaviors()) {
                for (Type takes : behavior.signature().takes()) {
                    namesIn(takes, named);
                }
                namesIn(behavior.signature().answers(), named);
            }
            for (CheckedHelper helper : module.helpers()) {
                for (CheckedHelper.Parameter parameter : helper.parameters()) {
                    namesIn(parameter.type(), named);
                }
            }
            for (Core body : bodiesOf(module)) {
                List<Core> nodes = new ArrayList<>();
                collect(body, Core.class, nodes);
                for (Core node : nodes) {
                    namesIn(node.type(), named);
                }
            }
        }
        return named;
    }

    /** The identities a value is laid out at: the four places a body says what one is made of. */
    private static Set<TypeSymbol.AtModule> everyIdentityLaidOutIn(CheckedProgram program) {
        Set<TypeSymbol.AtModule> named = new LinkedHashSet<>();
        for (CheckedModule module : program.modules()) {
            for (Core body : bodiesOf(module)) {
                List<Core.Construct> constructions = new ArrayList<>();
                collect(body, Core.Construct.class, constructions);
                for (Core.Construct construction : constructions) {
                    named.add(construction.typeName());
                }
                List<Core.UnitValue> units = new ArrayList<>();
                collect(body, Core.UnitValue.class, units);
                for (Core.UnitValue unit : units) {
                    namesIn(unit.data(), named);
                }
                List<Core.FieldAccess> reads = new ArrayList<>();
                collect(body, Core.FieldAccess.class, reads);
                for (Core.FieldAccess read : reads) {
                    namesIn(read.target().type(), named);
                }
                List<Core.Match> matches = new ArrayList<>();
                collect(body, Core.Match.class, matches);
                for (Core.Match match : matches) {
                    for (Core.Case arm : match.cases()) {
                        for (TypeSymbol selected : arm.caseTypes()) {
                            namesIn(selected, named);
                        }
                    }
                }
            }
        }
        return named;
    }

    /**
     * Every declaration {@code type} names, the ones inside a compound included.
     *
     * <p>Exhaustive over the sealed type rather than over the arms this test's fixtures happen to
     * produce: a walk written to the shapes at hand holds for those shapes, and a
     * {@code List<RoundingMode>} is as much a reader holding an identity as a bare one is.
     */
    private static void namesIn(Type type, Set<TypeSymbol.AtModule> named) {
        switch (type) {
            case Type.Ref ref -> namesIn(ref.name(), named);
            case Type.Union union -> {
                for (TypeSymbol member : union.members()) {
                    namesIn(member, named);
                }
            }
            // A compound names no declaration itself. What it holds is reached below, by the walk
            // that says once which positions each kind of compound has.
            case Type.Compound _ -> { }
            case Type.Prim _, Type.Nothing _, Type.Never _, Type.Erroneous _, Type.Open _ -> { }
        }
        Type.forEachChild(type, child -> namesIn(child, named));
    }

    /** The same, of a name: what the language gives directly is no declaration and is not one of
     *  these. */
    private static void namesIn(TypeSymbol name, Set<TypeSymbol.AtModule> named) {
        if (name instanceof TypeSymbol.AtModule at) {
            named.add(at);
        }
    }

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

    private static <T extends Core> void collect(Core from, Class<T> of, List<T> out) {
        if (of.isInstance(from)) {
            out.add(of.cast(from));
        }
        Core.forEachChild(from, child -> collect(child, of, out));
    }
}
