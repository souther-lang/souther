package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a type is made of, put together out of one answer for each sum it names, is what one descent
 * from all of those names reaches.
 *
 * <p>{@link AtomSpace#subjectAtoms} does not descend. It takes what {@link SumCases} answers for
 * each sum a type names — each made by a descent of its own — and lays them side by side, each
 * leaf once where it was first reached. One descent from every name goes through them in one walk,
 * sharing the sums already taken apart. The two are the same leaves in the same order only if a
 * sum met again from a second name contributes nothing the first did not, and that is what this
 * holds, against the descent itself ({@link AtomSpace#leavesUnder}).
 *
 * <p>Over every name of a module and every two of them, and not over the ones that looked
 * interesting. One name is held as well as two because one sum is handed on as its answer stands,
 * which is a way through of its own. The modules are a sum shared by two others, and two sums that
 * reach each other, which is refused where it is written and still has to come back the same.
 */
class WhatATypeIsMadeOfIsComposedOfEachSumsAnswerTest {

    /** A sum two others both list, under a sum that lists both of them. */
    private static final String SHARED = """
            module m

            data A
            data B
            data C
            data D
            data Shared = C | D
            data Left   = A | Shared
            data Right  = Shared | B
            data Top    = Left | Right
            """;

    /** Two sums each listing the other. */
    private static final String REACHING_EACH_OTHER = """
            module m

            data X
            data Y
            data P = Q | X
            data Q = P | Y
            """;

    @Test
    void aSumSharedByTwoOthersIsComposedAsOneDescentReachesIt() {
        Module shared = new Module(SHARED);

        assertEquals(List.of("A", "C", "D", "B"), shared.composed(Type.ref(shared.named("Top"))),
                "the shared sum's leaves stand where the first sum listing it reached them");
        shared.composesEveryTwoNamesAsOneDescent();
    }

    @Test
    void twoSumsReachingEachOtherAreComposedAsOneDescentReachesThem() {
        Module cyclic = new Module(REACHING_EACH_OTHER);

        assertEquals(List.of("Y", "X"), cyclic.composed(Type.ref(cyclic.named("P"))),
                "a sum reaching itself through another comes back with the leaves under both");
        cyclic.composesEveryTwoNamesAsOneDescent();
    }

    /** One module, read the way a check reads it: by form, and by what the declarations say. */
    private static final class Module {

        private final Hir.Module resolved;
        private final DeclarationKinds kinds;
        private final PublishedDeclarations said;
        private final SumCases sums;

        Module(String source) {
            resolved = Compilation.ofDocuments(Map.of("m.sou", source), Set.of(), ModulePath.EMPTY)
                    .db().ask(new Names.Resolved("m")).value();
            Symbols symbols = TypeChecker.symbols(resolved, DefaultStdlib.get());
            kinds = ScopedDeclarations.kindsOf(symbols);
            said = ScopedDeclarations.of(symbols);
            sums = SumCases.asWritten(kinds, said);
        }

        TypeSymbol named(String name) {
            for (Hir.Def d : resolved.defs()) {
                if (d.name().equals(name)) {
                    return d.declares();
                }
            }
            throw new AssertionError("the module does not declare " + name);
        }

        List<String> composed(Type type) {
            return shown(AtomSpace.subjectAtoms(type, kinds, sums));
        }

        /**
         * Every one of the module's names, and every union of two of them — sums, units, and one of
         * each — composed, and walked in one descent from the same names in the same order.
         */
        void composesEveryTwoNamesAsOneDescent() {
            List<TypeSymbol> names = new ArrayList<>();
            for (Hir.Def d : resolved.defs()) {
                names.add(d.declares());
            }
            for (TypeSymbol one : names) {
                assertEquals(shown(AtomSpace.leavesUnder(List.of(one), kinds, said)),
                        composed(Type.ref(one)), one::name);
            }
            int compared = 0;
            for (TypeSymbol first : names) {
                for (TypeSymbol second : names) {
                    if (first.equals(second)) {
                        continue;
                    }
                    Type.Union union = (Type.Union) Type.union(
                            new LinkedHashSet<>(List.of(first, second)));
                    assertEquals(shown(AtomSpace.leavesUnder(AtomSpace.statedBy(union), kinds,
                                    said)),
                            composed(union),
                            () -> first.name() + " | " + second.name());
                    compared++;
                }
            }
            int pairs = names.size() * (names.size() - 1);
            int seen = compared;
            assertTrue(seen == pairs && pairs > 0,
                    () -> "compared " + seen + " unions of the " + pairs + " there are");
        }

        private static List<String> shown(List<TypeSymbol> names) {
            return names.stream().map(TypeSymbol::name).toList();
        }
    }
}
