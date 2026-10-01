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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk over a type's guarantees reaches a value by is one node, however many names it went
 * down to get there, and it means what the field accesses written out would mean.
 *
 * <p>How far a walk goes is as long as the declarations chain, which nothing the author writes
 * bounds. Held as a field access per name, the value at the bottom would be as deep as the chain and
 * every reader of a rule written there would recurse that far. Held as one node, it has to be read
 * by every reader the way the accesses would be: wherever a clause is read again after the walk, and
 * wherever what a quantifier says is put to an element.
 *
 * <p>Read off the declarations directly rather than through a compile, for the reason
 * {@link ANewtypeChainIsReadOneNameAtATimeTest} gives.
 */
class AValueAGuaranteeWalkReachesIsOneNodeHoweverFarDownTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Long enough that a walk down it on the call stack does not fit in {@link #STACK}. */
    private static final int LINKS = 3000;

    private static final long STACK = 256L << 10;

    /** A chain of records each holding the next one down under {@code next}, and a rule only on the
     *  bottom one. */
    private static String recordChainOf(int links) {
        StringBuilder src = new StringBuilder("module demo exposing ( R1 )\n\n"
                + "data R1 = { amount: Int }\n    invariant amount >= 0\n");
        for (int i = 2; i <= links; i++) {
            src.append("data R").append(i).append(" = { next: R").append(i - 1).append(" }\n");
        }
        return src.toString();
    }

    private static final class Reading {

        private final RuleReadingSource rules;

        private final PathEngine engine;

        private final GuaranteeWalk walk;

        Reading(String source) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            rules = RuleReadings.of(compilation, compilation.modules().get(0));
            engine = new PathEngine(RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES),
                    Terms.Of.THE_DISCHARGE_TREE);
            walk = new GuaranteeWalk(engine.guarantees(),
                    DeclarationNewtypes.asWritten(rules.symbols()));
        }

        /** A place named {@code name} of the declared type {@code type}, entered in {@code at}. */
        Core.Read place(String name, Type type) {
            BindingId binding = CoreBinders
                    .of(new Hir.Binders(new BindingOwner.OfValue("demo", name)).binder(name, POS))
                    .binding();
            return new Core.Read(name, binding, type, POS);
        }

        Denotations entering(Denotations at, Core.Read place) {
            return at.location(place.binding(), engine.terms().placeSubject(place.binding()),
                    engine.terms().placeTerm(place.binding()));
        }

        /** Every guarantee a walk over {@code root} hears, with where it heard it. */
        List<Heard> walked(Core.Read root, Denotations at) {
            List<Heard> heard = new ArrayList<>();
            walk.from(root, RuleKey.THE_VALUE, at, GuaranteeWalk.Scope.everyName(),
                    (path, guarantee) -> heard.add(new Heard(path, guarantee)));
            return heard;
        }

        /** What a clause comes to read again in {@code at}, as the atoms its relations are over. */
        Set<FactSubject> atomsOf(Core clause, Denotations at) {
            Set<FactSubject> out = new HashSet<>();
            engine.predicates().assumed(clause, at, false, (_, _, _) -> { })
                    .relations().forEach(each -> out.addAll(each.atoms()));
            return out;
        }

        FactSubject subjectOf(Core e, Denotations at) {
            return engine.terms().subjectOf(e, at);
        }
    }

    private record Heard(RuleKey path, TypeGuarantee guarantee) {}

    private static Type declared(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey("demo", name)));
    }

    private static Core.FieldAccess access(Core target, String field, Type type) {
        return new Core.FieldAccess(target, field, type, POS);
    }

    /**
     * A chain of records is walked to its bottom on a stack it does not fit in, and the rule there
     * is read at the position as far down as the chain is long.
     *
     * <p>The other half of the newtype chain: every name here is a step, so the position grows with
     * the chain where a newtype's stays where it is.
     */
    @Test
    void aRuleUnderALongChainOfRecordsIsReadAtItsPosition() {
        List<Heard> heard = ALongChain.HEARD;

        // R1 writes the rule about its own field, so it is heard where R1 stands.
        List<String> steps = new ArrayList<>();
        for (int i = 2; i <= LINKS; i++) {
            steps.add("next");
        }
        assertEquals(1, heard.size());
        assertEquals(new RuleKey(steps), heard.getFirst().path());
        assertEquals(1, heard.getFirst().guarantee().owed().relations().size(),
                "the rule at the bottom states its relation");
    }

    /**
     * How deep the clause read at the bottom of a chain is does not turn on how long the chain is.
     *
     * <p>Asked of the tree and not of whether a reader ran out of stack. A reader that got through
     * a deep tree some other way would leave the depth where it was, and the next reader to recurse
     * over it would find it there.
     */
    @Test
    void theClauseReadAtTheBottomIsNoDeeperForALongerChain() {
        assertEquals(depthOf(heardAtTheBottomOf(2).getFirst().guarantee().clause()),
                depthOf(ALongChain.HEARD.getFirst().guarantee().clause()));
    }

    /** What a walk over a chain of {@code links} records hears, walked on a small stack. */
    private static List<Heard> heardAtTheBottomOf(int links) {
        Reading reading = new Reading(recordChainOf(links));
        Core.Read root = reading.place("v", declared("R" + links));
        Denotations at = reading.entering(Denotations.none(), root);
        return onASmallStack(() -> reading.walked(root, at));
    }

    /** The long chain, compiled and walked once for every question asked of it. */
    private static final class ALongChain {

        static final List<Heard> HEARD = heardAtTheBottomOf(LINKS);
    }

    /**
     * Two projections of as many names as the long chain has are compared, hashed and spelled on
     * a stack the chain does not fit in.
     *
     * <p>Built apart, so that no part of one is the other's and the comparison has to go along
     * every name. What the node is for is keeping how many names there are off the stack, and
     * names compared by recursing would put it back there.
     */
    @Test
    void manyNamesAreComparedHashedAndSpelledWithoutTheCallStack() {
        Core.Read root = new Core.Read("v", null, Type.INT, POS);
        Core.FieldProjection one = longProjection(root, "next");
        Core.FieldProjection same = longProjection(root, "next");
        Core.FieldProjection other = longProjection(root, "nxt");

        assertTrue(onASmallStack(() -> one.equals(same) && one.hashCode() == same.hashCode()
                && !one.equals(other) && one.toString().equals(same.toString())));
    }

    /** {@code root} with {@code first} read off it and then {@code next} as often as the chain is
     *  long. */
    private static Core.FieldProjection longProjection(Core root, String first) {
        Core.FieldProjection out = Core.FieldProjection.then(root, first, Type.INT);
        for (int i = 2; i <= LINKS; i++) {
            out = Core.FieldProjection.then(out, "next", Type.INT);
        }
        return out;
    }

    /** How many nodes the longest way down {@code e} has, counted on a stack of its own. */
    private static int depthOf(Core e) {
        record At(Core node, int depth) {}
        int deepest = 0;
        Deque<At> left = new ArrayDeque<>();
        left.push(new At(e, 1));
        while (!left.isEmpty()) {
            At here = left.pop();
            deepest = Math.max(deepest, here.depth());
            Core.forEachChild(here.node(), child -> left.push(new At(child, here.depth() + 1)));
        }
        return deepest;
    }

    /**
     * Where newtypes and records alternate, a record's field is a step of the position and a
     * newtype's {@code value} is not.
     */
    @Test
    void onlyARecordsFieldIsAStepOfThePosition() {
        Reading reading = new Reading("""
                module demo exposing ( N4 )

                data N0 = Int
                    invariant value >= 0
                data R1 = { f: N0 }
                data N2 = R1
                data R3 = { g: N2 }
                data N4 = R3
                """);
        Core.Read root = reading.place("v", declared("N4"));
        Denotations at = reading.entering(Denotations.none(), root);

        List<Heard> heard = reading.walked(root, at);

        assertEquals(List.of(new RuleKey(List.of("g", "f"))),
                heard.stream().map(Heard::path).toList());
    }

    /**
     * Two positions of one type hear one rule each, and the clause each heard is still about its own
     * position when it is read again after the walk.
     *
     * <p>Read again in the one environment the walk was given, which is what a reader holding the
     * clause after the walk has. A clause that took its meaning from somewhere only the walk had
     * would read the same at both positions, or at neither.
     */
    @Test
    void aClauseReadAgainAfterTheWalkIsStillAboutItsOwnPosition() {
        Reading reading = new Reading("""
                module demo exposing ( Pair )

                data NonNeg = Int
                    invariant value >= 0
                data Pair = { a: NonNeg, b: NonNeg }
                """);
        Core.Read root = reading.place("v", declared("Pair"));
        Denotations at = reading.entering(Denotations.none(), root);
        Type nonNeg = declared("NonNeg");

        List<Heard> heard = reading.walked(root, at);

        assertEquals(List.of("a", "b"), heard.stream().map(each -> each.path().toString()).toList());
        Set<FactSubject> a = reading.atomsOf(heard.get(0).guarantee().clause(), at);
        Set<FactSubject> b = reading.atomsOf(heard.get(1).guarantee().clause(), at);
        assertEquals(Set.of(reading.subjectOf(
                access(access(root, "a", nonNeg), "value", Type.INT), at)), a,
                "what the walk read at `a` is about `v.a.value` written out");
        assertEquals(Set.of(reading.subjectOf(
                access(access(root, "b", nonNeg), "value", Type.INT), at)), b);
        assertNotEquals(a, b);
    }

    /**
     * A projection is the place its accesses written out are, and a newtype's {@code value} on the
     * way is no step of it — and it is the same term they are.
     */
    @Test
    void aProjectionIsThePlaceItsAccessesWrittenOutAre() {
        Reading reading = new Reading("""
                module demo exposing ( Outer )

                data NonNeg = Int
                    invariant value >= 0
                data Inner = { amount: NonNeg }
                data Outer = { inner: Inner }
                """);
        Core.Read root = reading.place("v", declared("Outer"));
        Denotations at = reading.entering(Denotations.none(), root);
        Type inner = declared("Inner");
        Type nonNeg = declared("NonNeg");

        Core projected = Core.FieldProjection.then(Core.FieldProjection.then(
                Core.FieldProjection.then(root, "inner", inner), "amount", nonNeg),
                "value", Type.INT);
        Core written = access(access(access(root, "inner", inner), "amount", nonNeg),
                "value", Type.INT);

        Terms terms = reading.engine.terms();
        assertEquals(new Location(root.binding(), List.of("inner", "amount")),
                terms.locationOf(written, at));
        assertEquals(terms.locationOf(written, at), terms.locationOf(projected, at));
        assertEquals(TermMeaning.of(written), TermMeaning.of(projected));
        assertNotEquals(TermMeaning.of(access(access(root, "inner", inner), "amount", nonNeg)),
                TermMeaning.of(projected), "and the name a newtype wears is still a name read");
    }

    /**
     * The projections shorter than one are the subexpressions the accesses written out hold
     * between it and its base, the nearest first, and the base is not among them.
     */
    @Test
    void theShorterProjectionsAreTheAccessesBetweenItAndItsBase() {
        Reading reading = new Reading("""
                module demo exposing ( Outer )

                data NonNeg = Int
                    invariant value >= 0
                data Inner = { amount: NonNeg }
                data Outer = { inner: Inner }
                """);
        Core.Read root = reading.place("v", declared("Outer"));
        Type inner = declared("Inner");
        Type nonNeg = declared("NonNeg");
        Core.FieldProjection projected = Core.FieldProjection.then(Core.FieldProjection.then(
                Core.FieldProjection.then(root, "inner", inner), "amount", nonNeg),
                "value", Type.INT);

        List<TermMeaning> shorter = new ArrayList<>();
        projected.shorter().forEach(each -> shorter.add(TermMeaning.of(each)));
        List<TermMeaning> standing = new ArrayList<>();
        Core.subexpressionsAt(projected).forEach(each -> standing.add(TermMeaning.of(each)));
        List<Core> atARead = new ArrayList<>();
        Core.subexpressionsAt(root).forEach(atARead::add);

        Core written = access(access(access(root, "inner", inner), "amount", nonNeg),
                "value", Type.INT);
        assertEquals(List.of(
                TermMeaning.of(access(access(root, "inner", inner), "amount", nonNeg)),
                TermMeaning.of(access(root, "inner", inner))), shorter);
        assertEquals(List.of(TermMeaning.of(written),
                        TermMeaning.of(access(access(root, "inner", inner), "amount", nonNeg)),
                        TermMeaning.of(access(root, "inner", inner))), standing,
                "a walk asking each node meets the projection and then what the accesses held"
                        + " between it and the base, as it would have going down them");
        assertEquals(List.of(root), atARead, "and at any other node, the node alone");
    }

    /**
     * What a quantifier a guarantee states is put to an element of the container, and the
     * predicate keeps reading the position the walk reached.
     *
     * <p>The predicate names a field of the value the walk reached as well as the element, so
     * putting the element in is a substitution into a tree that holds what the walk reached by. Both
     * are read where the element is put, in the environment of whoever puts it.
     */
    @Test
    void aQuantifierPutToAnElementKeepsReadingThePositionTheWalkReached() {
        Reading reading = new Reading("""
                module demo exposing ( Holder )

                data Line = { quantity: Int }
                data Order = { cap: Int, lines: List<Line> }
                    invariant List.all(i -> i.quantity <= cap, lines)
                data Holder = { order: Order }
                """);
        Core.Read root = reading.place("v", declared("Holder"));
        Core.Read element = reading.place("e", declared("Line"));
        Denotations at = reading.entering(reading.entering(Denotations.none(), root), element);

        List<Heard> heard = reading.walked(root, at);

        assertEquals(1, heard.size());
        List<Quantified> said = heard.getFirst().guarantee().quantified();
        assertEquals(1, said.size());
        Known put = reading.engine.predicates()
                .instantiate(said.getFirst(), element, Known.top(), at);
        FactSubject cap = reading.subjectOf(
                access(access(root, "order", declared("Order")), "cap", Type.INT), at);
        FactSubject quantity = reading.subjectOf(access(element, "quantity", Type.INT), at);
        assertTrue(put.speaksOf(cap), "the predicate reads `v.order.cap`");
        assertTrue(put.speaksOf(quantity), "and the element it was put to");
        assertNotEquals(cap, quantity, "and the two are two values");
    }

    private static <T> T onASmallStack(Supplier<T> asked) {
        AtomicReference<T> answered = new AtomicReference<>();
        AtomicReference<Throwable> failed = new AtomicReference<>();
        Thread asking = new Thread(null, () -> {
            try {
                answered.set(asked.get());
            } catch (Throwable e) {
                failed.set(e);
            }
        }, "a small stack", STACK);
        asking.start();
        try {
            asking.join();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
        if (failed.get() != null) {
            throw new AssertionError("asked on a small stack", failed.get());
        }
        return answered.get();
    }
}
