package souther.compiler.check;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

/**
 * What an atom answers is settled by the atoms read before it, so the atoms a form is read through
 * are read in one order — the order a computation was recorded for them in — whichever form asks,
 * however it was written, and whether or not the run of answers it takes is kept for the forms that
 * begin with it.
 *
 * <p>The order was whatever a map handed its keys over in, which is not the same from one run to the
 * next, and a run kept by which atoms it holds and not by their order took the atoms of one form in
 * the order of another. Both are held here: the run is the order, and the answers come to the same
 * with the runs kept and without them.
 */
class AFormIsReadThroughItsAtomsInTheOrderTheyWereRecordedInTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static BindingId binding(int index) {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), index);
    }

    private static Core.Read number(BindingId of) {
        return new Core.Read("n", of, Type.INT, POS);
    }

    /** What a naming of {@code atoms} records, handed to {@link #chain}. */
    private record Named(Terms terms, List<FactSubject> atoms) {}

    private static Named named(int atoms) {
        Terms terms = RuleReadings.termsOfNoClauseFiled(Symbols.none(DefaultStdlib.get()),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        for (int each = 0; each < atoms; each++) {
            at = at.location(binding(each), AsPlaces.of(binding(each)), AsPlaces.term(binding(each)));
        }
        List<FactSubject> subjects = new ArrayList<>();
        for (int each = 0; each < atoms; each++) {
            subjects.add(terms.atomOf(number(binding(each)), at));
        }
        return new Named(terms, subjects);
    }

    /** Each atom a product of the sum of the ones before it, which is how a chain of names reads. */
    private static void chain(Named named) {
        List<FactSubject> atoms = named.atoms();
        for (int each = 1; each < atoms.size(); each++) {
            Map<FactSubject, ExactRatio> before = new LinkedHashMap<>();
            for (int earlier = 0; earlier < each; earlier++) {
                before.put(atoms.get(earlier), ExactRatio.ONE);
            }
            LinearForm<FactSubject> sum = new LinearForm<>(ExactRatio.ZERO, before);
            named.terms().computedBy(atoms.get(each), new AtomKnowledge.Computation.Derived(
                    new Derivation.Product(sum, sum)));
        }
    }

    private static LinearForm<FactSubject> over(Random dice, List<FactSubject> atoms, int most) {
        Map<FactSubject, ExactRatio> coefs = new LinkedHashMap<>();
        int named = 2 + dice.nextInt(most);
        for (int each = 0; each < named; each++) {
            coefs.put(atoms.get(dice.nextInt(atoms.size())), ExactRatio.ONE);
        }
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    @Test
    void theRunOfAFormIsTheOrderItsAtomsAreReadInAndThatIsTheOrderTheyWereRecordedIn() {
        Named chain = named(14);
        chain(chain);
        Random dice = new Random(3210);
        int forms = 0;
        for (int round = 0; round < 200; round++) {
            LinearForm<FactSubject> form = over(dice, chain.atoms(), 6);
            List<FactSubject> run = DerivedNumericFacts.runOf(form, chain.terms());
            assertEquals(DerivedNumericFacts.readingOrderOf(form, chain.terms()), run);
            List<FactSubject> recorded = new ArrayList<>(run);
            recorded.sort((one, other) -> Integer.compare(chain.terms().recordedAt(one),
                    chain.terms().recordedAt(other)));
            assertEquals(recorded, run, "a run is in the order its atoms were recorded in");
            forms++;
        }
        assertTrue(forms > 100);
    }

    /**
     * What an atom says, from a naming whose atoms were recorded in the order {@code recorded} puts
     * them in. The same recipes and the same relations in every order, so that what each says is
     * asked of the order alone — an atom met again while it is being derived answers nothing, and
     * which that is depends on which was read first.
     */
    private static List<DerivedNumericFacts.Says> saysWhenRecordedIn(int atoms, long seed,
                                                                    List<Integer> recorded) {
        Named named = named(atoms);
        List<FactSubject> subjects = named.atoms();
        Random dice = new Random(seed);
        Map<Integer, LinearForm<FactSubject>> over = new LinkedHashMap<>();
        for (int each = 1; each < atoms; each++) {
            Map<FactSubject, ExactRatio> two = new LinkedHashMap<>();
            two.put(subjects.get(dice.nextInt(each)), ExactRatio.ONE);
            two.put(subjects.get(dice.nextInt(each)), ExactRatio.ONE.negated());
            over.put(each, new LinearForm<>(ExactRatio.ZERO, two));
        }
        for (int each : recorded) {
            if (each >= 1) {
                named.terms().computedBy(subjects.get(each), new AtomKnowledge.Computation.Derived(
                        new Derivation.Product(over.get(each), over.get(each))));
            }
        }
        for (int each = 0; each < atoms; each++) {
            FactSubject here = subjects.get(each);
            FactSubject there = subjects.get(dice.nextInt(atoms));
            if (!here.equals(there)) {
                named.terms().carrying(here, List.of(new NumericConstraint(
                        LinearForm.difference(here, there), Rel.LE)));
            }
        }
        return saysOfEach(named);
    }

    /**
     * Which atom answers nothing because it is met again while it is derived is a matter of which
     * was read first, and the order a form is read in was whatever a map handed its atoms over in.
     * Held to no difference between the orders atoms are recorded in, over rings of recipes and of
     * relations: the one order they are read in now is then one of the orders they could have been
     * read in before, each of which answered alike.
     */
    @Test
    void noOrderTheAtomsAreRecordedInSaysMoreThanTheOrderTheRecipesWereNamedIn() {
        int differing = 0;
        int saying = 0;
        for (long seed = 0; seed < 40; seed++) {
            int atoms = 9;
            List<Integer> forwards = new ArrayList<>();
            for (int each = 0; each < atoms; each++) {
                forwards.add(each);
            }
            List<DerivedNumericFacts.Says> first = saysWhenRecordedIn(atoms, seed, forwards);
            if (first.stream().anyMatch(each -> !(each instanceof DerivedNumericFacts.Says.Nothing))) {
                saying++;
            }
            Random dice = new Random(seed + 1000);
            for (int order = 0; order < 5; order++) {
                List<Integer> shuffled = new ArrayList<>(forwards);
                Collections.shuffle(shuffled, dice);
                List<DerivedNumericFacts.Says> other = saysWhenRecordedIn(atoms, seed, shuffled);
                for (int at = 0; at < first.size(); at++) {
                    assertTrue(atLeastAsTight(first.get(at), other.get(at)), "atom " + at + " recorded in "
                            + shuffled + " says " + other.get(at) + " where recorded in the order the"
                            + " recipes were named in it says " + first.get(at));
                    if (!first.get(at).equals(other.get(at))) {
                        differing++;
                    }
                }
            }
        }
        assertTrue(saying > 10, "too few of the atoms said anything for this to hold anything: " + saying);
        assertTrue(differing > 0, "no order said anything but what the recorded one did, so the order"
                + " is not what this is held to");
    }

    /** Whether {@code tight} says all that {@code loose} does, and as much more as it says. */
    private static boolean atLeastAsTight(DerivedNumericFacts.Says tight,
                                          DerivedNumericFacts.Says loose) {
        if (loose instanceof DerivedNumericFacts.Says.Nothing || tight.equals(loose)) {
            return true;
        }
        if (!(tight instanceof DerivedNumericFacts.Says.These inner)
                || !(loose instanceof DerivedNumericFacts.Says.These outer)
                || inner.facts().size() != outer.facts().size()) {
            return false;
        }
        for (int at = 0; at < inner.facts().size(); at++) {
            if (inner.facts().get(at).equals(outer.facts().get(at))) {
                continue;
            }
            if (!(inner.facts().get(at) instanceof DerivedNumericFacts.Fact.Between(FactSubject one,
                            NumericDomain.Bounds within))
                    || !(outer.facts().get(at) instanceof DerivedNumericFacts.Fact.Between(
                            FactSubject other, NumericDomain.Bounds without))
                    || !one.equals(other) || !endsWithin(within, without)) {
                return false;
            }
        }
        return true;
    }

    private static boolean endsWithin(NumericDomain.Bounds within, NumericDomain.Bounds without) {
        return (without.min() == null || (within.min() != null
                && tighterOrEqual(within.min(), without.min(), 1)))
                && (without.max() == null || (within.max() != null
                && tighterOrEqual(within.max(), without.max(), -1)));
    }

    /** Whether {@code one} is at least as far in as {@code other}, which is above it for a least end
     *  ({@code sign} 1) and below it for a greatest ({@code -1}). */
    private static boolean tighterOrEqual(Endpoint one, Endpoint other, int sign) {
        int by = sign * ((Count) one.at()).at().compareTo(((Count) other.at()).at());
        return by > 0 || (by == 0 && (other.inclusive() || !one.inclusive()));
    }

    @Test
    void aFormThatReadsTheAtomsOfAnotherAndOneMoreBeginsWithItsRun() {
        Named chain = named(8);
        chain(chain);
        List<FactSubject> atoms = chain.atoms();
        for (int length = 2; length <= atoms.size(); length++) {
            Map<FactSubject, ExactRatio> shorter = new LinkedHashMap<>();
            Map<FactSubject, ExactRatio> longer = new LinkedHashMap<>();
            for (int at = 0; at < length; at++) {
                longer.put(atoms.get(at), ExactRatio.ONE);
                if (at < length - 1) {
                    shorter.put(atoms.get(at), ExactRatio.ONE);
                }
            }
            List<FactSubject> before = DerivedNumericFacts.runOf(
                    new LinearForm<>(ExactRatio.ZERO, shorter), chain.terms());
            List<FactSubject> after = DerivedNumericFacts.runOf(
                    new LinearForm<>(ExactRatio.ZERO, longer), chain.terms());
            assertEquals(before, after.subList(0, before.size()),
                    "the atoms of the longer form begin with the atoms of the shorter");
        }
    }

    @Test
    void theRunDoesNotDependOnHowTheFormWasWritten() {
        Named chain = named(8);
        chain(chain);
        List<FactSubject> atoms = chain.atoms();
        Map<FactSubject, ExactRatio> forwards = new LinkedHashMap<>();
        Map<FactSubject, ExactRatio> backwards = new LinkedHashMap<>();
        for (int at = 0; at < atoms.size(); at++) {
            forwards.put(atoms.get(at), ExactRatio.ONE);
            backwards.put(atoms.get(atoms.size() - 1 - at), ExactRatio.ONE);
        }
        assertEquals(DerivedNumericFacts.runOf(new LinearForm<>(ExactRatio.ZERO, forwards), chain.terms()),
                DerivedNumericFacts.runOf(new LinearForm<>(ExactRatio.ZERO, backwards), chain.terms()));
    }

    /** What every atom of {@code named} answers, as the facts it says. */
    private static List<DerivedNumericFacts.Says> saysOfEach(Named named) {
        NumericDomain<FactSubject> nothing = Known.top().numbers();
        List<DerivedNumericFacts.Says> out = new ArrayList<>();
        for (FactSubject atom : named.atoms()) {
            out.add(DerivedNumericFacts.saysOf(atom, nothing, named.terms()));
        }
        return out;
    }

    private static List<DerivedNumericFacts.Says> readWithRunsAndWithout(Named kept, Named apart) {
        apart.terms().derivationPlans.keepNone();
        List<DerivedNumericFacts.Says> with = saysOfEach(kept);
        assertEquals(with, saysOfEach(apart), "read with the runs kept and without them");
        return with;
    }

    @Test
    void aChainOfNamesAnswersTheSameWithTheRunsKeptAsWithoutThem() {
        Named kept = named(10);
        Named apart = named(10);
        chain(kept);
        chain(apart);
        readWithRunsAndWithout(kept, apart);
    }

    /**
     * Atoms that carry a relation to one another, so that reading one of them reaches the next and
     * the next reaches the first again: an atom met while it is being derived answers nothing, and
     * which atom that is depends on the order they were read in.
     */
    private static void ringed(Named named, Random dice) {
        List<FactSubject> atoms = named.atoms();
        for (int each = 1; each < atoms.size(); each++) {
            Map<FactSubject, ExactRatio> two = new LinkedHashMap<>();
            two.put(atoms.get(dice.nextInt(each)), ExactRatio.ONE);
            two.put(atoms.get(dice.nextInt(each)), ExactRatio.ONE.negated());
            LinearForm<FactSubject> from = new LinearForm<>(ExactRatio.ZERO, two);
            named.terms().computedBy(atoms.get(each), new AtomKnowledge.Computation.Derived(
                    new Derivation.Product(from, from)));
        }
        for (int each = 0; each < atoms.size(); each++) {
            FactSubject here = atoms.get(each);
            FactSubject there = atoms.get(dice.nextInt(atoms.size()));
            if (!here.equals(there)) {
                named.terms().carrying(here, List.of(new NumericConstraint(
                        LinearForm.difference(here, there), Rel.LE)));
            }
        }
    }

    @Test
    void atomsThatCarryRelationsToOneAnotherAnswerTheSameWithTheRunsKeptAsWithoutThem() {
        int rings = 0;
        for (int seed = 0; seed < 40; seed++) {
            Named kept = named(9);
            Named apart = named(9);
            ringed(kept, new Random(seed));
            ringed(apart, new Random(seed));
            List<DerivedNumericFacts.Says> said = readWithRunsAndWithout(kept, apart);
            if (said.stream().anyMatch(each -> !(each instanceof DerivedNumericFacts.Says.Nothing))) {
                rings++;
            }
        }
        assertTrue(rings > 10, "too few of the atoms said anything for this to hold anything: " + rings);
    }

    @Test
    void theRunsAreLetGoWhereSomethingIsRecordedAboutAnAtomTheyWereMadeFrom() {
        Named chain = named(6);
        List<FactSubject> atoms = chain.atoms();
        chain.terms().computedBy(atoms.get(1), new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(atoms.get(0)), LinearForm.atom(atoms.get(0)))));
        Map<FactSubject, ExactRatio> both = new LinkedHashMap<>();
        both.put(atoms.get(1), ExactRatio.ONE);
        both.put(atoms.get(2), ExactRatio.ONE);
        LinearForm<FactSubject> form = new LinearForm<>(ExactRatio.ZERO, both);
        assertEquals(List.of(atoms.get(1)), DerivedNumericFacts.runOf(form, chain.terms()),
                "atom 2 has no computation yet, so the form is read through atom 1 only");
        chain.terms().computedBy(atoms.get(2), new AtomKnowledge.Computation.Derived(
                new Derivation.Product(LinearForm.atom(atoms.get(1)), LinearForm.atom(atoms.get(1)))));
        assertEquals(List.of(atoms.get(1), atoms.get(2)), DerivedNumericFacts.runOf(form, chain.terms()),
                "and through both once it has");
        assertEquals(Set.of(atoms.get(1), atoms.get(2)),
                Set.copyOf(DerivedNumericFacts.readingOrderOf(form, chain.terms())));
    }
}
