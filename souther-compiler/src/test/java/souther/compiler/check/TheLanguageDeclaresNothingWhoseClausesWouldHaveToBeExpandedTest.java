package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The language declares no {@link Hir.Data}, so no declaration of its own has clauses that would
 * have to be expanded.
 *
 * <p>A fence and not a rule. Every declaration whose clauses a reading takes is expanded in the
 * environment of the module that wrote it, and the language's own declarations are in no module of
 * a compilation — there is nothing to expand them in. That costs nothing today because the only
 * kinds the language declares are a sum and its cases, and {@link Hir.SumData} and
 * {@link Hir.UnitData} carry no {@code invariant} at all.
 *
 * <p>What this holds is that the situation stays the one that costs nothing. The day the language
 * declares a {@code data} — with a clause or without one — this goes red, and whoever wrote it has
 * to say where its clauses are expanded before anything reads them. Written the other way round,
 * as "no language declaration writes a clause", it would pass a {@code data} that wrote none and
 * leave the next one to be read as stating nothing.
 *
 * <p>Not a claim that the language may not declare one. It is a claim that this compiler has no
 * answer for one yet, said where it is cheap to say rather than found where a rule went unread.
 */
class TheLanguageDeclaresNothingWhoseClausesWouldHaveToBeExpandedTest {

    @Test
    void theLanguageDeclaresNoDataAtAll() {
        List<String> data = new ArrayList<>();
        for (Map.Entry<TypeKey, Hir.Def> declared
                : DefaultStdlib.get().languageDeclarations().entrySet()) {
            if (declared.getValue() instanceof Hir.Data) {
                data.add(declared.getKey().qualified());
            }
        }
        assertEquals(List.of(), data,
                "a declaration of the language's own with clauses to expand has nowhere to be"
                        + " expanded: every expansion runs in the module that wrote the declaration,"
                        + " and no module of a compilation wrote these");
    }

    /** And the kinds it does declare are the ones the HIR gives no clauses. */
    @Test
    void whatItDeclaresIsSumsAndTheirCases() {
        List<String> other = new ArrayList<>();
        for (Map.Entry<TypeKey, Hir.Def> declared
                : DefaultStdlib.get().languageDeclarations().entrySet()) {
            if (!(declared.getValue() instanceof Hir.SumData)
                    && !(declared.getValue() instanceof Hir.UnitData)) {
                other.add(declared.getKey().qualified() + " is a "
                        + declared.getValue().getClass().getSimpleName());
            }
        }
        assertEquals(List.of(), other,
                "the kinds the language declares are the ones with no invariant to write");
    }
}
