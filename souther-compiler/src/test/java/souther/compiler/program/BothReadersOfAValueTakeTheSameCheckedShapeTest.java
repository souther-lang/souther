package souther.compiler.program;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.observe.FieldTypes;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a value's parts are read against is one answer, and both readers of a row carry it whole.
 *
 * <p>The compile reads a text and runs what it names; an output outside this compiler is handed a
 * snapshot. Each reads a value's fields, and each takes them from what the check settled a value of
 * the declaration is made of — so a row means the same thing wherever it is read. What is fixed
 * here is that neither projection drops or reshapes anything on the way: a field a spread brought
 * in, a newtype's one field, a base with type arguments, and a set — whose declaration is what says
 * the order it stands in is not part of it.
 */
class BothReadersOfAValueTakeTheSameCheckedShapeTest {

    /**
     * A declaration of each kind the two readings could have come apart over.
     *
     * <p>{@code Wide} takes a field through a spread and declares a {@code Set} of its own,
     * {@code Yen} is a newtype over a primitive, and {@code Stock} is one over a type with
     * arguments. {@code Holder} holds values of two of them, which is what makes the program's
     * closure over its declarations something to ask about.
     */
    private static final String MODULE = """
            module demo

            data Base = { tag: String }
            data Wide =
                { ...Base
                , kinds: Set<String>
                }
            data Yen = Int
            data Stock = Map<String, Int>
            data Holder =
                { base: Base
                , prices: List<Yen>
                }
            """;

    /** Every declaration the snapshot holds. */
    private static List<CheckedData> declarationsOf(CheckedProgram program) {
        List<CheckedData> all = new ArrayList<>(program.languageDeclarations());
        for (CheckedModule module : program.modules()) {
            all.addAll(module.data());
        }
        return all;
    }

    /** What this compile answers about a value's fields, which is what the rows are read against. */
    private static FieldTypes compileSide(Compilation c) {
        Symbols symbols = Scopes.derived(c.db(), c.modules().get(0)).value();
        return Shapes.fieldTypes(c.db(), symbols);
    }

    private static Compilation compiled() {
        Compilation c = Compilation.ofSource(MODULE, "Main");
        c.answerEverything();
        return c;
    }

    /** And the shape itself is what the declarations wrote, so the agreement below is about
     *  something. */
    @Test
    void whatTheCheckSettledIsWhatTheDeclarationsWrote() {
        FieldTypes fields = compileSide(compiled());
        assertEquals(List.of("tag", "kinds"), List.copyOf(fields.of(named("Wide")).keySet()),
                "a spread's field comes first and the declaration's own after it");
        assertInstanceOf(Type.SetOf.class, fields.of(named("Wide")).get("kinds"),
                "the field is declared a set, which is what says its order is not part of it");
        assertEquals(Type.INT, fields.of(named("Yen")).get("value"),
                "a newtype holds the one field it is written with");
        assertInstanceOf(Type.MapOf.class, fields.of(named("Stock")).get("value"),
                "and a base with type arguments keeps them");
    }

    /** The two readers answer alike about every declaration the program holds. */
    @Test
    void andBothReadersAnswerAlikeAboutEveryDeclaration() {
        Compilation c = compiled();
        FieldTypes compile = compileSide(c);
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        List<CheckedData> declarations = declarationsOf(program);
        FieldTypes snapshot = DeclaredFields.over(declarations);
        assertTrue(declarations.size() > 4, "the walk reached the declarations: " + declarations);
        for (CheckedData each : declarations) {
            assertEquals(snapshot.of(each.name()), compile.of(each.name()),
                    "the compile and the snapshot read `" + each.name() + "` differently");
        }
    }

    /**
     * And a declaration the snapshot does not hold is refused rather than read as a value with no
     * such field.
     *
     * <p>A program is closed over the declarations its values can name. Read as an absence, a value
     * of one left out would be compared as whatever its parts happen to look like — which is the
     * one thing a row may not mean.
     */
    @Test
    void andADeclarationTheProgramDoesNotHoldIsRefused() {
        FieldTypes snapshot = DeclaredFields.over(List.of());
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> snapshot.of(named("Wide")));
        assertTrue(refused.getMessage().contains("Wide"), refused.getMessage());
    }

    /**
     * And the program holds every declaration its values' fields name.
     *
     * <p>The closure the reading above rests on. A field holding a value of a declaration is a
     * place a reader descends into, and the declaration it descends by has to be here — one left
     * out is a value read as whatever its parts look like rather than as what it is. Said of the
     * program itself rather than of what a row happens to state, because the next reader of a
     * checked program will descend somewhere this one does not.
     */
    @Test
    void andTheProgramHoldsEveryDeclarationItsFieldsName() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        int named = 0;
        for (CheckedData each : declarationsOf(program)) {
            if (!(each instanceof CheckedData.Product product)) {
                continue;
            }
            for (souther.compiler.core.ValueShape.Field field : product.fields()) {
                for (TypeSymbol reached : declarationsIn(field.type())) {
                    if (reached instanceof TypeSymbol.AtModule at) {
                        named++;
                        program.declaration(at);   // refuses what this program does not hold
                    }
                }
            }
        }
        assertTrue(named > 0, "no field of this program names a declaration, so nothing was asked");
    }

    /** Every declaration a type names, wherever in it they stand. */
    private static List<TypeSymbol> declarationsIn(Type type) {
        List<TypeSymbol> out = new ArrayList<>();
        switch (type) {
            case Type.Ref(TypeSymbol name) -> out.add(name);
            case Type.Union(java.util.Set<TypeSymbol> members) -> out.addAll(members);
            case Type.ListOf(Type element) -> out.addAll(declarationsIn(element));
            case Type.SetOf(Type element) -> out.addAll(declarationsIn(element));
            case Type.OptionOf(Type element) -> out.addAll(declarationsIn(element));
            case Type.MapOf(Type key, Type value) -> {
                out.addAll(declarationsIn(key));
                out.addAll(declarationsIn(value));
            }
            case Type.TupleOf(List<Type> elements) -> elements.forEach(e ->
                    out.addAll(declarationsIn(e)));
            case Type.FnOf(List<Type> params, Type result) -> {
                params.forEach(p -> out.addAll(declarationsIn(p)));
                out.addAll(declarationsIn(result));
            }
            case Type.Prim _, Type.Nothing _, Type.Never _, Type.Erroneous _, Type.Open _ -> { }
        }
        return out;
    }

    private static TypeSymbol named(String data) {
        return TypeSymbols.declared(new TypeKey("demo", data));
    }

    /** Nothing the language gives is a declaration a module left out, so asking about one is not a
     *  question about this program's closure. */
    @Test
    void andWhatTheLanguageGivesIsAnsweredWithoutFields() {
        assertEquals(Map.of(),
                DeclaredFields.over(List.of()).of(new TypeSymbol.Primitive(Type.Prim.INT)));
    }
}
