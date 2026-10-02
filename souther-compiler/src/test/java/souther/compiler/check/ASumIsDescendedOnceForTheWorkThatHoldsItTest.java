package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reader recording its reads holds answers as the descent does, and descends each sum once.
 *
 * <p>{@link SumCases#asWrittenOnceEach} is for a reader that cannot take the compilation's answer
 * because it records what it reads, and that asks one sum of many classes. Its answers are the
 * descent's, and a sum asked again is answered without reading what any declaration says — which
 * is what lets such a reader pay for a sum once and still record everything it read.
 */
class ASumIsDescendedOnceForTheWorkThatHoldsItTest {

    private static final String MODULE = """
            module m

            data A
            data B
            data C
            data Inner = B | C
            data Outer = A | Inner
            data Card = { no: String }
            data Mixed = Card | A
            """;

    private final Hir.Module resolved = Compilation.ofDocuments(Map.of("m.sou", MODULE), Set.of(),
            ModulePath.EMPTY).db().ask(new Names.Resolved("m")).value();
    private final Symbols symbols = TypeChecker.symbols(resolved, DefaultStdlib.get());
    private final DeclarationKinds kinds = ScopedDeclarations.kindsOf(symbols);
    private final PublishedDeclarations said = ScopedDeclarations.of(symbols);

    @Test
    void itAnswersAsTheDescentDoesForEveryName() {
        SumCases descent = SumCases.asWritten(kinds, said);
        SumCases once = SumCases.asWrittenOnceEach(kinds, said);
        for (TypeSymbol.AtModule name : names()) {
            assertEquals(descent.of(name), once.of(name), name::name);
            assertEquals(descent.of(name), once.of(name), () -> name.name() + ", asked again");
        }
    }

    @Test
    void aSumAskedAgainReadsNothing() {
        AtomicInteger reads = new AtomicInteger();
        PublishedDeclarations counted = declaration -> {
            reads.incrementAndGet();
            return said.of(declaration);
        };
        SumCases once = SumCases.asWrittenOnceEach(kinds, counted);
        TypeSymbol.AtModule outer = named("Outer");

        once.of(outer);
        int first = reads.get();
        once.of(outer);

        assertTrue(first > 0, "the first ask descends what the sum says");
        assertEquals(first, reads.get(), "and the second reads nothing");
    }

    private List<TypeSymbol.AtModule> names() {
        return resolved.defs().stream()
                .map(Hir.Def::declares)
                .map(TypeSymbol.AtModule.class::cast)
                .toList();
    }

    private TypeSymbol.AtModule named(String name) {
        return names().stream().filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("the module does not declare " + name));
    }
}
