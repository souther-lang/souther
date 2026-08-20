package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What {@code Symbols.reach} writes for a type resolves back to that type.
 *
 * <p>A section of {@code Symbols.resolve} and not its inverse. {@code Amount}, {@code up.Amount}
 * and {@code lib.Amount} may all reach one declaration, so there is no inverse to have; {@code
 * reach} picks one of them, and the one it picks is read back as the type it was asked about. A
 * pair that does not compose is a reference the compiler produced and the compiler will not read,
 * which is the whole of what a generated row being writable means.
 *
 * <p>Read back by whichever reader reads the position the name is written at. For a declaration
 * that is {@code resolve}; for the language's own vocabulary — a primitive, the runtime's error
 * cases — {@code resolve} answers nothing at all and {@code resolveCase} is the reader. Both are
 * held below, so where the section stops being about {@code resolve} is written down rather than
 * left out of the list.
 *
 * <p>Held over every declaration a module can meet rather than over cases picked out here. A
 * spelling that happens to round-trip for the type it was written for says nothing about the one
 * beside it: the answers differ by whether the bare name is taken, by which module declares it, and
 * by whether that module exposes it, and none of those is visible in a name.
 */
class AReachedNameResolvesBackToWhatItWasAskedAboutTest {

    private static final String LIB = """
            module lib exposing ( Shown, Sum, One, Two )

            data Shown = Int
            data Hidden = String

            data One
            data Two
            data Sum = One | Two
            """;

    /** Every way of reaching another module at once, beside a declaration of its own. */
    private static final String APP = """
            module app exposing ( Own, In, f )

            import lib as up
            import lib ( Shown )

            data Own = { n: Int }
            data RoundingMode = { tag: String }

            data In = { n: Int }

            behavior f : (i: In) -> Own constructs Own
            let f (i) = Own { n = i.n }
            """;

    private static Symbols scopeOf(String module, String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), module).value();
    }

    /** Every declaration this compilation has, which is what a position here may turn out to be. */
    private static List<TypeSymbol> everyDeclaration() {
        List<TypeSymbol> named = new ArrayList<>();
        for (String each : List.of("Shown", "Hidden", "One", "Two", "Sum")) {
            named.add(TypeSymbols.declared(new TypeKey("lib", each)));
        }
        for (String each : List.of("Own", "RoundingMode", "In")) {
            named.add(TypeSymbols.declared(new TypeKey("app", each)));
        }
        named.add(TypeSymbol.runtime("RoundingMode"));
        return named;
    }

    /** What {@code reach} answers resolves back to the type it was asked about. */
    @Test
    void whatIsWrittenForATypeResolvesToThatType() {
        Symbols symbols = scopeOf("app", LIB, APP);

        List<String> broken = new ArrayList<>();
        for (TypeSymbol type : everyDeclaration()) {
            if (symbols.scope().reach(type) instanceof TypeReachName.Written written) {
                if (!type.equals(symbols.scope().resolve(spelled(written.rendered())).type())) {
                    broken.add(written.rendered() + " is written for " + type + " and resolves to "
                            + symbols.scope().resolve(spelled(written.rendered())).type());
                }
            }
        }

        assertEquals(List.of(), broken);
    }

    /** And what it says has no name here has none — no spelling this module can write reaches it. */
    @Test
    void whatHasNoNameHereIsNotReachedByAnySpellingThisModuleWrites() {
        Symbols symbols = scopeOf("app", LIB, APP);

        List<TypeSymbol> unnameable = new ArrayList<>();
        for (TypeSymbol type : everyDeclaration()) {
            if (symbols.scope().reach(type) instanceof TypeReachName.Unnameable u) {
                unnameable.add(u.denotes());
            }
        }

        assertEquals(List.of(TypeSymbols.declared(new TypeKey("lib", "Hidden")), TypeSymbol.runtime("RoundingMode")),
                unnameable, "one its module keeps to itself, one this module took the spelling of");
        for (TypeSymbol type : unnameable) {
            for (String spelling : List.of(type.name(), type.qualified(),
                    "up." + type.name(), "lib." + type.name())) {
                assertFalse(type.equals(symbols.scope().resolve(spelled(spelling)).type()),
                        "`" + spelling + "` reaches " + type + " after all");
            }
        }
    }

    /**
     * The case the law is about, on its own: a module that declares the spelling the language's own
     * data has takes it, and the language's has no other (ADR-0087). Answered bare, the reference
     * would resolve to this module's declaration — a different type, and one that compiles.
     */
    @Test
    void aRuntimeBackedTypeThisModuleTookTheSpellingOfHasNoNameHere() {
        TypeSymbol language = TypeSymbol.runtime("RoundingMode");

        assertInstanceOf(TypeReachName.Unnameable.class, scopeOf("app", LIB, APP).scope().reach(language));
        assertEquals(TypeSymbols.declared(new TypeKey("app", "RoundingMode")),
                scopeOf("app", LIB, APP).scope().resolve(spelled("RoundingMode")).type());
    }

    /** And where nothing here took it, it is written as itself. */
    @Test
    void aRuntimeBackedTypeNothingHereShadowsIsWrittenBare() {
        Symbols symbols = scopeOf("lib", LIB, APP);
        TypeSymbol language = TypeSymbol.runtime("RoundingMode");

        assertEquals("RoundingMode", assertInstanceOf(TypeReachName.Written.class,
                symbols.scope().reach(language)).rendered());
        assertEquals(language, symbols.scope().resolve(spelled("RoundingMode")).type());
    }

    /**
     * The language's own vocabulary is written as itself, and read back by the reader that reads a
     * case rather than by {@code resolve}, which says nothing about either of them.
     *
     * <p>Here rather than left out of {@link #everyDeclaration()}: a section is a section on a
     * domain, and a domain nothing states is one a later reader assumes is everything. These reach
     * a position — a primitive heads a union a behavior answers with, and the runtime's failures
     * are its cases — so a writer meets them and has to be told what they are written as.
     */
    @Test
    void theLanguagesOwnVocabularyIsWrittenAsItselfAndReadBackAsACase() {
        Symbols symbols = scopeOf("app", LIB, APP);

        for (TypeSymbol vocabulary : List.of(TypeSymbol.primitive("Int"),
                TypeSymbol.runtime("DivisionByZero"))) {
            TypeReachName.Written written = assertInstanceOf(TypeReachName.Written.class,
                    symbols.scope().reach(vocabulary), vocabulary.toString());

            assertEquals(vocabulary.name(), written.rendered());
            assertEquals(vocabulary, symbols.scope().resolveCase(spelled(written.rendered())).type(),
                    "the reader of the position a case name stands at");
            assertEquals(Denotation.NOT_IN_SCOPE, symbols.scope().resolve(spelled(written.rendered())),
                    "and not this one, which answers for declarations");
        }
    }

    /** A spelling this test composes, as the resolver takes one: a name no source wrote,
     *  which is what a reach name rendered back is. */
    private static WrittenName spelled(String spelling) {
        return WrittenName.synthetic(spelling, null);
    }
}
