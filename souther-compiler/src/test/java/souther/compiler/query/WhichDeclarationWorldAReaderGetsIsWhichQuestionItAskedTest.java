package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A module has two declaration worlds, and which one a reader is holding is which question it asked.
 *
 * <p>They used to be one question with a value attached — a {@code Stage} handed to the registry —
 * so a reader wanting the derived declarations and a reader wanting the resolved ones asked the same
 * thing and were told apart by what they passed. Nothing in what either was holding said which it
 * had, and passing the other value was a mistake that typed.
 *
 * <p>What tells them apart now is the query. This is what the difference is: a clause naming a
 * helper is a call to it in one world, and in the other it is the rule that helper states, with the
 * constructions written in it written as constructions.
 */
class WhichDeclarationWorldAReaderGetsIsWhichQuestionItAskedTest {

    private static final String SOURCE = """
            module m exposing ( Amount, Wrapped )

            data Wrapped = Int
            data Amount = Int
                invariant isOk(value)

            let isOk (n: Int) : Bool = Wrapped(n) == Wrapped(0)
            """;

    private static Db db() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY).db();
    }

    private static Hir.Expr clauseOf(Symbols symbols) {
        Hir.Def def = symbols.declarations().declaration(new TypeKey("m", "Amount"));
        return ((Hir.Data) def).invariants().get(0).expr();
    }

    @Test
    void theResolvedWorldAndTheDerivedWorldAnswerDifferently() {
        Db db = db();

        Hir.Expr resolved = clauseOf(Names.resolvedSymbols(db, "m").value());
        Hir.Expr derived = clauseOf(Names.derivedSymbols(db, "m").value());

        assertEquals(1, applications(resolved),
                "the resolved world holds the clause as written: a call to the helper");
        assertEquals(0, applications(derived),
                "the derived world holds the rule that helper states, its constructions written as "
                        + "constructions");
        assertNotEquals(resolved, derived, "so the two worlds are not the same answer");
    }

    /** And a reader of either holds a declaration, not a choice about which world to read. */
    @Test
    void neitherScopeCarriesWhichWorldItCameFrom() {
        Db db = db();

        assertInstanceOf(Symbols.class, Names.resolvedSymbols(db, "m").value());
        assertInstanceOf(Symbols.class, Names.derivedSymbols(db, "m").value());
    }

    private static int applications(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] found = {e instanceof Hir.Apply ? 1 : 0};
        Hir.forEachChild(e, c -> found[0] += applications(c));
        return found[0];
    }
}
