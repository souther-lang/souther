package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.test.OnItsOwnStack;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of newtypes is read one name at a time, and walked without the call stack.
 *
 * <p>Nothing here changes an answer, which is why it is held on its own: what a value guarantees is
 * the same whether a reading takes every name off at every link or only the one on the outside, and
 * whether a walk goes down on the call stack or on its own. The readings that fix the answers pass
 * either way, while the first costs the rest of the chain at every link and the second runs out of
 * room on a chain long enough.
 *
 * <p>Read off the declarations directly rather than through a compile. How many values a newtype
 * has is asked of the next one down through the query store, which nests as deep as the chain, and
 * a compile of a long chain stops there before it reaches these.
 */
class ANewtypeChainIsReadOneNameAtATimeTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Long enough that a walk down it on the call stack does not fit in {@link #STACK}. */
    private static final int LINKS = 3000;

    private static final long STACK = 256L << 10;

    /** The only rule in the chain is on the bottom of it, so a reading that finds it has been all
     *  the way down. */
    private static String chainOf(int links) {
        StringBuilder src = new StringBuilder("module demo exposing ( T1 )\n\n"
                + "data T1 = Int\n    invariant value >= 0\n");
        for (int i = 2; i <= links; i++) {
            src.append("data T").append(i).append(" = T").append(i - 1).append('\n');
        }
        return src.toString();
    }

    private static RuleReadingSource rules(int links) {
        Compilation compilation = Compilation.ofSource(chainOf(links), "Main");
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static Type top(int links) {
        return Type.ref(TypeSymbols.declared(new TypeKey("demo", "T" + links)));
    }

    /** What a value written under the outermost of a hundred names is, asked of what each name
     *  wraps once: the name on the outside, and nothing under it. */
    @Test
    void aValueUnderManyNamesAsksWhatTheOutermostWrapsOnce() {
        int links = 100;
        RuleReadingSource rules = rules(links);
        AtomicInteger asked = new AtomicInteger();
        NewtypeInners counting = declaration -> {
            asked.incrementAndGet();
            return rules.inners().of(declaration);
        };

        ValueReading reading = ValueReading.of(top(links), counting, rules.kinds(),
                rules.symbols(), rules.published());

        assertEquals(1, asked.get());
        assertEquals(List.of(NewtypeInners.THE_ONE_VALUE), List.copyOf(reading.named().keySet()));
        assertEquals(top(links - 1), reading.named().get(NewtypeInners.THE_ONE_VALUE));
    }

    /**
     * The walk goes to the bottom of a long chain and reads the rule written there.
     *
     * <p>Read, and not only reached. The value under every name of the chain is that name's
     * {@code value} of the value over it, so the value the rule is read against is reached by as
     * many names as the chain has; what holds is that reading it states the relation the rule
     * writes, on a stack the chain does not fit in.
     */
    @Test
    void theWalkGoesDownALongChainWithoutTheCallStack() {
        RuleReadingSource rules = rules(LINKS);
        PathEngine engine = new PathEngine(
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES),
                Terms.Of.THE_DISCHARGE_TREE);
        GuaranteeWalk walk = new GuaranteeWalk(engine.guarantees(),
                DeclarationNewtypes.asWritten(rules.symbols()));
        BindingId binding = CoreBinders
                .of(new Hir.Binders(new BindingOwner.OfValue("demo", "v")).binder("v", POS))
                .binding();
        Core.Read root = new Core.Read("v", binding, top(LINKS), POS);
        Denotations at = Denotations.none().location(binding,
                engine.terms().placeSubject(binding), engine.terms().placeTerm(binding));
        List<String> heard = new ArrayList<>();

        onASmallStack(() -> {
            walk.from(root, RuleKey.THE_VALUE, at, GuaranteeWalk.Scope.everyName(),
                    new GuaranteeWalk.Reader() {
                        @Override
                        public void guaranteed(RuleKey path, TypeGuarantee guarantee) {
                            heard.add(path + " guaranteed " + guarantee.rule().clause()
                                    + " stating " + guarantee.owed().relations().size());
                        }

                        @Override
                        public void stopped(RuleKey path, Type type, GuaranteeWalk.Stop why) {
                            heard.add(why + " at " + type);
                        }
                    });
            return null;
        });

        // Every name of the chain is a newtype's `value`, which reaches no further position, so the
        // rule is heard at the value itself.
        assertEquals(List.of(RuleKey.THE_VALUE + " guaranteed T1#0 stating 1"), heard);
    }

    @Test
    void whetherARuleStandsUnderALongChainIsAnsweredFromTheBottom() {
        RuleReadingSource rules = rules(LINKS);
        PathEngine engine = new PathEngine(
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES),
                Terms.Of.THE_DISCHARGE_TREE);

        assertTrue(onASmallStack(() -> engine.guarantees().anyRuleUnder(top(LINKS))));
    }

    private static <T> T onASmallStack(Supplier<T> asked) {
        return OnItsOwnStack.ask("asked on a small stack", STACK, asked);
    }
}
