package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a name is written twice, whether the declaration came out is asked of the one the module
 * has.
 *
 * <p>A name written twice is one declaration and one mistake: the first is what the module
 * declares and the second is reported and left out, which is settled once and read from there by
 * every stage. Whether a declaration came out has to be settled for the same one — read off the
 * second, it answers about a declaration nothing else in the compiler is holding, and the module
 * that does declare a perfectly good `A` is told it has no meaning.
 */
class ADeclarationWrittenTwiceIsAnsweredForByTheOneTheModuleHasTest {

    private static Compilation compiled(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    private static boolean has(Compilation c, String declared) {
        return c.db().ask(new Names.Definition(new TypeKey("m.a", declared))).present();
    }

    /** The second `A` names nothing; the first, which is the one the module has, is made of `Int`. */
    @Test
    void theDeclarationTheModuleHasKeepsItsMeaningWhateverTheRejectedOneIsMadeOf() {
        Compilation c = compiled("""
                module m.a exposing ( A )

                data A = { value: Int }
                data A = { value: Nowhere }
                """);

        assertTrue(has(c, "A"), "what `m.a` declares as `A` is made of `Int`");
    }
}
