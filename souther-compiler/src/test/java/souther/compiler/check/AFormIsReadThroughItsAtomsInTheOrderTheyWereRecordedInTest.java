package souther.compiler.check;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
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
        DerivedNumericFacts.withoutRuns = false;
        List<DerivedNumericFacts.Says> with = saysOfEach(kept);
        DerivedNumericFacts.withoutRuns = true;
        try {
            assertEquals(with, saysOfEach(apart), "read with the runs kept and without them");
        } finally {
            DerivedNumericFacts.withoutRuns = false;
        }
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
