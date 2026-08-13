package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeName;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * {@code Symbols.reach} is the inverse of {@code Symbols.resolve}, and is held to it.
 *
 * <p>The two are one relation read in two directions: {@code resolve} takes what a module wrote and
 * answers the declaration, {@code reach} takes the declaration and answers what this module writes.
 * A pair that does not compose is a reference the compiler produced and the compiler will not read
 * — which is the whole of what a generated row being writable means.
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
        return compilation.db().ask(new Shapes.Scope(module)).value();
    }

    /** Every declaration this compilation has, which is what a position here may turn out to be. */
    private static List<TypeName> everyDeclaration() {
        List<TypeName> named = new ArrayList<>();
        for (String each : List.of("Shown", "Hidden", "One", "Two", "Sum")) {
            named.add(new TypeName("lib", each));
        }
        for (String each : List.of("Own", "RoundingMode", "In")) {
            named.add(new TypeName("app", each));
        }
        named.add(TypeName.runtime("RoundingMode"));
        return named;
    }

    /** What {@code reach} answers resolves back to the type it was asked about. */
    @Test
    void whatIsWrittenForATypeResolvesToThatType() {
        Symbols symbols = scopeOf("app", LIB, APP);

        List<String> broken = new ArrayList<>();
        for (TypeName type : everyDeclaration()) {
            if (symbols.reach(type) instanceof TypeReachName.Written written) {
                if (!type.equals(symbols.resolve(written.rendered()))) {
                    broken.add(written.rendered() + " is written for " + type + " and resolves to "
                            + symbols.resolve(written.rendered()));
                }
            }
        }

        assertEquals(List.of(), broken);
    }

    /** And what it says has no name here has none — no spelling this module can write reaches it. */
    @Test
    void whatHasNoNameHereIsNotReachedByAnySpellingThisModuleWrites() {
        Symbols symbols = scopeOf("app", LIB, APP);

        List<TypeName> unnameable = new ArrayList<>();
        for (TypeName type : everyDeclaration()) {
            if (symbols.reach(type) instanceof TypeReachName.Unnameable u) {
                unnameable.add(u.denotes());
            }
        }

        assertEquals(List.of(new TypeName("lib", "Hidden"), TypeName.runtime("RoundingMode")),
                unnameable, "one its module keeps to itself, one this module took the spelling of");
        for (TypeName type : unnameable) {
            for (String spelling : List.of(type.name(), type.qualified(),
                    "up." + type.name(), "lib." + type.name())) {
                assertFalse(type.equals(symbols.resolve(spelling)),
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
        TypeName language = TypeName.runtime("RoundingMode");

        assertInstanceOf(TypeReachName.Unnameable.class, scopeOf("app", LIB, APP).reach(language));
        assertEquals(new TypeName("app", "RoundingMode"),
                scopeOf("app", LIB, APP).resolve("RoundingMode"));
    }

    /** And where nothing here took it, it is written as itself. */
    @Test
    void aRuntimeBackedTypeNothingHereShadowsIsWrittenBare() {
        Symbols symbols = scopeOf("lib", LIB, APP);
        TypeName language = TypeName.runtime("RoundingMode");

        assertEquals("RoundingMode", assertInstanceOf(TypeReachName.Written.class,
                symbols.reach(language)).rendered());
        assertEquals(language, symbols.resolve("RoundingMode"));
    }
}
