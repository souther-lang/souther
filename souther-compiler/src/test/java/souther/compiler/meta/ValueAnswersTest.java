package souther.compiler.meta;

import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a module records a value as is read back as the same type, whatever the type is made of. A
 * type that came back as another one would type a call to the value's entry as something the value
 * is not.
 */
class ValueAnswersTest {

    private static final Type.Ref STEP =
            new Type.Ref(TypeSymbols.declared(new TypeKey("shared.pricing", "Step")));

    @Test
    void aTypeIsReadBackAsItself() {
        SequencedSet<TypeSymbol> members = new LinkedHashSet<>();
        members.add(TypeSymbols.declared(new TypeKey("shared.pricing", "Step")));
        members.add(new TypeSymbol.LanguageCase(LanguageCaseId.DIVISION_BY_ZERO));
        members.add(TypeSymbol.primitive(Type.Prim.INT));

        List<Type> types = List.of(
                Type.Prim.INT,
                Type.Prim.DECIMAL,
                new Type.Nothing(),
                STEP,
                new Type.ListOf(STEP),
                new Type.SetOf(Type.Prim.STRING),
                new Type.OptionOf(new Type.ListOf(Type.Prim.INT)),
                new Type.MapOf(Type.Prim.STRING, new Type.OptionOf(STEP)),
                new Type.TupleOf(List.of(Type.Prim.INT, STEP)),
                new Type.FnOf(List.of(Type.Prim.INT, STEP), new Type.ListOf(Type.Prim.BOOL)),
                new Type.FnOf(List.of(), Type.Prim.INT),
                new Type.Union(members));

        for (Type type : types) {
            assertEquals(type, ValueAnswers.decode(ValueAnswers.encode(type)),
                    () -> "written as " + ValueAnswers.encode(type));
        }
    }

    @Test
    void aTypeStillOpenIsNotAnAnswer() {
        assertNull(ValueAnswers.encode(new Type.Var("a", false)));
        assertNull(ValueAnswers.encode(new Type.ListOf(new Type.Var("a", false))));
    }

    @Test
    void textThatWritesNoTypeReadsAsNone() {
        for (String text : List.of("", "List(", "List(Int", "Map(Int)", "Ref(@shared.pricing)",
                "Ref(?x)", "Nope", "Int)", "Fn(Int,Int)")) {
            assertNull(ValueAnswers.decode(text), text);
        }
    }
}
