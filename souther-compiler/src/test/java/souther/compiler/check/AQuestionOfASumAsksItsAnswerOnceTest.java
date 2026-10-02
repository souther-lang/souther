package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One question about a value of a sum asks the sum's answer once.
 *
 * <p>The answer holds both what a value of the sum can be and whether every leaf is a unit, so a
 * reader wanting both takes it once and reads each off it. One that checks the arm and then goes
 * back through what a type is made of for the leaves asks the same sum again — which, under the
 * walk a scope-only reading is handed, is the sum descended twice for one question.
 *
 * <p>Held for each reader that wants both, and for an enumeration and a sum that is none, since
 * the readers part on which arm it is.
 */
class AQuestionOfASumAsksItsAnswerOnceTest {

    private static final String MODULE = """
            module m

            data Prospecting
            data Won
            data Stage = Prospecting | Won

            data Card = { no: String }
            data Payment = Card | Won
            """;

    private final Hir.Module resolved = Compilation.ofDocuments(Map.of("m.sou", MODULE), Set.of(),
            ModulePath.EMPTY).db().ask(new Names.Resolved("m")).value();
    private final Symbols symbols = TypeChecker.symbols(resolved, DefaultStdlib.get());
    private final DeclarationKinds kinds = ScopedDeclarations.kindsOf(symbols);
    private final SumCases descended = ScopedDeclarations.sumsOf(symbols);
    private final NewtypeInners inners = NewtypeInners.asWritten(symbols);

    @Test
    void howASumCrossesAsksItOnce() {
        asksOnce(sums -> Boundary.of(stage(), kinds, sums));
        asksOnce(sums -> Boundary.of(payment(), kinds, sums));
    }

    @Test
    void whatASumIsAsAPositionAsksItOnce() {
        asksOnce(sums -> TypeView.shapeOf(stage(), inners, symbols, kinds, sums));
        asksOnce(sums -> TypeView.shapeOf(payment(), inners, symbols, kinds, sums));
    }

    @Test
    void whatTheModelWritesWhereASumStandsAsksItOnce() {
        asksOnce(sums -> ValueReading.of(stage(), inners, kinds, symbols, sums));
        asksOnce(sums -> ValueReading.of(payment(), inners, kinds, symbols, sums));
    }

    private void asksOnce(Consumer<SumCases> question) {
        AtomicInteger asked = new AtomicInteger();
        SumCases counted = sum -> {
            asked.incrementAndGet();
            return descended.of(sum);
        };
        question.accept(counted);
        assertEquals(1, asked.get(), "the sum's answer was asked for one question");
    }

    private Type stage() {
        return Type.ref(named("Stage"));
    }

    private Type payment() {
        return Type.ref(named("Payment"));
    }

    private TypeSymbol named(String name) {
        for (Hir.Def d : resolved.defs()) {
            if (d.name().equals(name)) {
                return d.declares();
            }
        }
        throw new AssertionError("the module does not declare " + name);
    }
}
