package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a value carries by being what it is, held against the atom rather than against a reader.
 *
 * <p>The rules themselves have tests of their own — that a size is never negative, that an absolute
 * value is not, that a shift states what it moved by. Those pass while a reader that cannot reach
 * them exists, which is what #988 was: the facts were collected by walking an expression, so a
 * reading that had forms and atoms and no expression answered as though nothing were known of
 * anything it named. What is fixed here is therefore not the rules but where their answer lives and
 * who can reach it.
 *
 * <p>So these are tests about structure. Each one names a way the arrangement could come apart again
 * without any rule being wrong and without any diagnostic changing.
 */
class WhatAValueCarriesBelongsToTheAtomTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName LENGTH = new ValueName.Stdlib("List", "length");

    private static BindingId binding(int index) {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), index);
    }

    private static Terms terms() {
        return new Terms(Symbols.none(), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    private static Core.Read list(BindingId of) {
        return new Core.Read("xs", of, new Type.ListOf(Type.INT), POS);
    }

    private static Core.Read number(BindingId of) {
        return new Core.Read("n", of, Type.INT, POS);
    }

    private static Core length(Core of) {
        return new Core.PreservedCall(LENGTH, List.of(of), Type.INT, POS);
    }

    private static Core distinct(Core of) {
        return new Core.PreservedCall(new ValueName.Stdlib("List", "distinct"), List.of(of),
                of.type(), POS);
    }

    private static Denotations holding(BindingId... bindings) {
        Denotations at = Denotations.none();
        for (BindingId one : bindings) {
            at = at.location(one, AsPlaces.of(one), AsPlaces.term(one));
        }
        return at;
    }

    /** A size names an atom, and what that atom carries is filed where it was named. Nothing asks an
     * expression for it, which is the whole of what #988 turned on. */
    @Test
    void namingASizeFilesWhatItCarries() {
        Terms terms = terms();
        BindingId xs = binding(0);
        FactSubject atom = terms.atomOf(length(list(xs)), holding(xs));

        assertNotNull(atom, "a size over a nameable container is an atom");
        assertTrue(terms.knowledgeOf(atom).intrinsic().stream()
                        .anyMatch(one -> one.rel() == Rel.GE
                                && one.form().equals(LinearForm.atom(atom))),
                "and it carries that it is at or above nought, filed against itself");
    }

    /**
     * A size that stands to another size carries that relation, and the value at the other end of it
     * is reached.
     *
     * <p>The case a reader working reachability out from the recipes alone would drop. Nothing
     * computes {@code List.length(List.distinct(xs))} from {@code List.length(xs)} — one is no
     * recipe over the other — and a reading that did not reach the second would take the relation in
     * against a value it had left unspoken for.
     */
    @Test
    void whatARelationNamesIsReached() {
        Terms terms = terms();
        BindingId xs = binding(0);
        Denotations at = holding(xs);
        FactSubject narrowed = terms.atomOf(length(distinct(list(xs))), at);
        FactSubject whole = terms.atomOf(length(list(xs)), at);

        assertNotNull(narrowed);
        assertNotNull(whole);
        assertTrue(terms.knowledgeOf(narrowed).directlyReads(narrowed).contains(whole),
                "reading what a filtered container's size carries reads the size it came from");
        assertTrue(terms.reached(LinearForm.atom(narrowed)).contains(whole),
                "so the closure reaches it, and a place is kept for it (#988)");
    }

    /**
     * One value carries one thing, however many readings name it.
     *
     * <p>A container written out and the same container reached through a name are one value, so the
     * size of either is one atom. Answered differently by the two routes, what an atom carried would
     * depend on which reader got to it first, and the reader that asked between them would be
     * answered out of half of it.
     */
    @Test
    void oneAtomCarriesOneAnswerWhicheverRouteNamedIt() {
        Terms terms = terms();
        BindingId xs = binding(0);
        BindingId ys = binding(1);
        Terms naming = terms;
        Denotations outer = holding(xs);
        Core built = distinct(list(xs));
        // Entered as a `let` does it: a name for a value, and no location — a binding with one is a
        // place, and a place is named by where it is rather than by what it was given.
        Denotations at = outer.binding(ys, built, naming.subjectOf(built, outer),
                null, naming.bodyKey(built, outer), null);

        FactSubject written = terms.atomOf(length(distinct(list(xs))), at);
        FactSubject named = terms.atomOf(
                length(new Core.Read("ys", ys, new Type.ListOf(Type.INT), POS)), at);

        assertEquals(written, named, "one value, so one atom");
        assertEquals(terms.knowledgeOf(written).intrinsic(), terms.knowledgeOf(named).intrinsic(),
                "and one answer about what it carries");
    }

    /** And two answers about one atom are refused rather than merged: merging leaves the reading
     * that asked in between answered out of half of one. */
    @Test
    void twoAnswersAboutWhatOneAtomCarriesAreRefused() {
        Terms terms = terms();
        BindingId xs = binding(0);
        FactSubject atom = terms.atomOf(length(list(xs)), holding(xs));

        assertThrows(Terms.OneTermTwoIntrinsicAnswers.class, () -> terms.carrying(atom,
                List.of(new NumericConstraint(LinearForm.atom(atom), Rel.LE))));
    }

    /**
     * And saying nothing is not one of the two answers.
     *
     * <p>One value is named by more than one writing of it, and a writing the reading cannot make
     * out the operation behind — a library operation applied bare — comes back with nothing. That is
     * this reader having nothing to read and not the value carrying nothing, so it leaves what was
     * answered standing. Treated as an answer, what an atom carried would turn on which writing of
     * it the naming reached first.
     */
    @Test
    void sayingNothingLeavesTheAnswerStanding() {
        Terms terms = terms();
        BindingId xs = binding(0);
        FactSubject atom = terms.atomOf(length(list(xs)), holding(xs));
        List<NumericConstraint> answered = terms.knowledgeOf(atom).intrinsic();

        terms.carrying(atom, List.of());

        assertFalse(answered.isEmpty(), "the reading that could read it answered");
        assertEquals(answered, terms.knowledgeOf(atom).intrinsic(),
                "and the one that could not left that answer where it was");
    }

    /**
     * One value is reached one way, and the two ways of reaching one are one sum.
     *
     * <p>Held as a table of recipes beside a table of walks, each checked itself for a second entry
     * and neither checked the other, so an atom could stand in both — and the reader that asked was
     * answered by whichever table it looked in first.
     */
    @Test
    void anAtomIsNotReachedTwoWays() {
        Terms terms = terms();
        FactSubject atom = AsPlaces.of(binding(0));
        FactSubject other = AsPlaces.of(binding(1));
        terms.computedBy(atom, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(other), LinearForm.atom(other))));

        assertThrows(Terms.OneTermTwoDerivations.class, () -> terms.computedBy(atom,
                new AtomKnowledge.Computation.Reduction(new InductiveBounds.Walk(
                        LinearForm.constant(java.math.BigDecimal.ZERO), other,
                        LinearForm.atom(other), StepInputFacts.none()))));
    }

    /**
     * The two graphs an atom stands in have different cycles, and only one of them is an error.
     *
     * <p>A computation is written over strictly smaller expressions, so an atom reached from itself
     * that way is this check having named a value built out of itself. What a value carries relates
     * it to whatever it relates it to, with no such ordering: two values each no greater than the
     * other are two true statements. Written as one walk, one of the two answers would be wrong —
     * either a legitimate pair of relations reported as an internal disagreement, or a value built
     * out of itself walked until it ran out of stack.
     */
    @Test
    void aCycleThroughWhatValuesCarryIsNotACycleThroughHowTheyAreComputed() {
        Terms terms = terms();
        FactSubject one = AsPlaces.of(binding(0));
        FactSubject two = AsPlaces.of(binding(1));
        terms.carrying(one, List.of(new NumericConstraint(
                LinearForm.atom(one).minus(LinearForm.atom(two)), Rel.LE)));
        terms.carrying(two, List.of(new NumericConstraint(
                LinearForm.atom(two).minus(LinearForm.atom(one)), Rel.LE)));

        assertEquals(Set.of(one, two), terms.reached(LinearForm.atom(one)),
                "the closure stops on repetition, which is what a visited set is for");

        Terms computed = terms();
        computed.computedBy(one, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(one), LinearForm.atom(two))));

        assertThrows(DerivedNumericFacts.AnAtomComputedFromItself.class,
                () -> DerivedNumericFacts.refine(nothingKnown(), computed, Set.of(one)),
                "and an atom computed from itself is refused where it is derived");
    }

    /**
     * A cycle that only closes through what a value carries is not a value built out of itself.
     *
     * <p>The two graphs again, and this time on the stack rather than in the tables. Reading a
     * recipe reads the values a relation drags in, and reading one of those reads its own operands —
     * so a derivation can arrive back at an atom it is in the middle of without any computation
     * having reached itself. Here {@code a} is computed from {@code c}, {@code c} carries a relation
     * naming {@code b}, and {@code b} is computed from {@code a}: over computations alone that is
     * {@code a → c} and {@code b → a} and no cycle at all.
     *
     * <p>What is fixed is only that this is not called a disagreement. Deriving nothing for such an
     * atom is a reading that says less, which is what a reading that cannot see round a cycle should
     * say; refusing it says the naming built a value out of itself, which is a claim about this
     * check and is false here.
     */
    @Test
    void aCycleThatCrossesWhatAValueCarriesIsNotOneAtomComputedFromItself() {
        Terms terms = terms();
        Denotations at = holding(binding(0), binding(1), binding(2));
        FactSubject a = terms.atomOf(number(binding(0)), at);
        FactSubject b = terms.atomOf(number(binding(1)), at);
        FactSubject c = terms.atomOf(number(binding(2)), at);
        terms.computedBy(a, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(c), LinearForm.atom(c))));
        terms.computedBy(b, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(a), LinearForm.atom(a))));
        terms.carrying(c, List.of(new NumericConstraint(
                LinearForm.atom(c).minus(LinearForm.atom(b)), Rel.LE)));

        assertDoesNotThrow(() -> DerivedNumericFacts.refine(nothingKnown(), terms, Set.of(a)),
                "no computation reaches itself here, and only the relation closes the ring");

        // And the chain of recipes still answers for itself. Starting it again where the reading
        // steps across a relation must not stop it noticing a ring made of recipes alone, which
        // this one is: two of them and neither names itself.
        Terms round = terms();
        Denotations places = holding(binding(0), binding(1));
        FactSubject one = round.atomOf(number(binding(0)), places);
        FactSubject two = round.atomOf(number(binding(1)), places);
        round.computedBy(one, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(two), LinearForm.atom(two))));
        round.computedBy(two, new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(one), LinearForm.atom(one))));

        assertThrows(DerivedNumericFacts.AnAtomComputedFromItself.class,
                () -> DerivedNumericFacts.refine(nothingKnown(), round, Set.of(one)),
                "a ring of recipes is a value built out of itself however many recipes long it is");
    }

    /**
     * A value that carries something and computes nothing is not a recipe evaluated.
     *
     * <p>What the accounting states is that a reading does no work the question cannot reach, and it
     * counts recipes put through a reading. A size has no recipe and never had one; counted as work
     * done, the measure would start answering about how much the reading was handed rather than
     * about how much of it was evaluated twice.
     */
    @Test
    void whatAValueCarriesIsNoRecipeEvaluated() {
        Terms terms = terms();
        BindingId xs = binding(0);
        FactSubject atom = terms.atomOf(length(list(xs)), holding(xs));
        List<List<FactSubject>> watching = new ArrayList<>();
        DerivedNumericFacts.WATCHING = watching;
        try {
            DerivedNumericFacts.refine(nothingKnown(), terms, Set.of(atom));
        } finally {
            DerivedNumericFacts.WATCHING = null;
        }

        assertFalse(watching.stream().anyMatch(one -> one.contains(atom)),
                "it was taken into the reading, which is not a recipe being put through one");
    }

    /**
     * Nothing evaluates a recipe against a domain that has not been made a reading.
     *
     * <p>The one rule here that a reader could otherwise break by writing four correct lines. Both
     * stages have to happen and in that order, and a rule of that shape written down is a rule the
     * next caller does not read — so the second stage takes a type only the first stage makes, and
     * this fixes that it stays that way. Checked over the parameters and not over the callers: what
     * would go wrong is a new caller, and a test naming today's callers is a test that says nothing
     * about it.
     */
    @Test
    void aRecipeIsOnlyEvaluatedAgainstAReading() {
        List<String> takingARawDomain = new ArrayList<>();
        for (Method method : DerivedNumericFacts.class.getDeclaredMethods()) {
            for (Class<?> parameter : method.getParameterTypes()) {
                if (parameter.equals(NumericDomain.class) && !method.getName().equals("refine")
                        && !method.getName().equals("readingOf")) {
                    takingARawDomain.add(method.getName());
                }
            }
        }

        assertEquals(List.of(), takingARawDomain,
                "a domain reaches a recipe through `readingOf` or it does not reach one");

        // And the other way in, which the parameters say nothing about: a reading anybody can make
        // is a first stage anybody can skip. As a record this was open to the whole package, since a
        // record's canonical constructor is as accessible as the record and this one has to be seen
        // from `InductiveBounds`.
        for (var made : DerivedNumericFacts.ReadingDomain.class.getDeclaredConstructors()) {
            assertTrue(java.lang.reflect.Modifier.isPrivate(made.getModifiers()),
                    "a reading is made where the first stage is run, and nowhere else");
        }
    }

    private static NumericDomain<FactSubject> nothingKnown() {
        return Known.top().numbers();
    }
}
