package souther.compiler.meta;

import souther.compiler.check.Preserved;
import souther.compiler.core.CompleteSignature;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.ValueName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

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

    /** A name is counted and never lexed, so whatever the language lets a name hold is carried:
     * a letter outside the basic plane, and a combining mark that only continues a name. */
    @Test
    void aNameTheLanguageAcceptsIsCarriedWhateverItHolds() {
        for (String name : List.of("𝐀mount", "Café", "Ab_1", "金額")) {
            Type type = new Type.ListOf(new Type.Ref(TypeSymbols.declared(
                    new TypeKey("shared." + name, name))));

            assertEquals(type, ValueAnswers.decode(ValueAnswers.encode(type)), name);
        }
    }

    /** Only what the module publishes is recorded: a module settles more definitions than it
     * offers, and the rest are no values a reader can name. */
    @Test
    void onlyWhatTheModulePublishesIsRecorded() {
        ValueName.Helper cap = new ValueName.Helper("pricing", "cap");
        ValueName.Helper entry = new ValueName.Helper("pricing", "$value.cap");
        ValueName.Helper row = new ValueName.Helper("pricing", "$row.0");
        Preserved.SettledValues settled = new Preserved.SettledValues(Map.of(
                cap, CompleteSignature.ofSettledValue(cap, STEP),
                entry, CompleteSignature.ofSettledValue(entry, STEP),
                row, CompleteSignature.ofSettledValue(row, STEP)));

        List<String> written = ValueAnswers.written("pricing", Set.of("cap"), settled);

        assertEquals(1, written.size(), written.toString());
        assertEquals(Set.of(cap), ValueAnswers.read("pricing", written).signatures().keySet());
    }

    /** A published value settled as a type still open is a check that did not finish, and it is
     * said so rather than left out of what the module records. */
    @Test
    void aPublishedValueSettledAsAnOpenTypeIsAnInvariantViolation() {
        ValueName.Helper open = new ValueName.Helper("pricing", "open");
        Preserved.SettledValues settled = new Preserved.SettledValues(Map.of(
                open, CompleteSignature.ofSettledValue(open, new Type.Var("a", false))));

        assertThrows(IllegalStateException.class,
                () -> ValueAnswers.written("pricing", Set.of("open"), settled));
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
