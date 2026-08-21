package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading whose alternatives are held one at a time is the implementation there was before they
 * were held at all.
 *
 * <p>The claim a union of products rests on. What is held is a finite union of boxes, and the
 * reading that came before is the same union bounded at one box: a choice concatenates and is
 * merged back into the smallest box holding both, which is what "keep only what both sides spoke
 * about" already was. If that is so, the change of representation moves nothing, and the precision
 * that arrives later arrives by lifting the bound rather than by a second reading.
 *
 * <p><b>Said of readings built the same way and not of readings written out.</b> Two states with
 * the same values may have been reached by different rules, and what a reading answers turns on how
 * it was reached — so every state here is a term over the constructors and connectives, evaluated
 * once against each implementation. A term that comes out different names the shape that broke it.
 *
 * <p>What is compared is the surface a reader has. Nothing outside this package reads the parts of
 * a reading, so an equivalence about them would hold the representation still rather than the
 * answers, which is the opposite of what this is for.
 */
class AReadingHeldAsOneBoxIsThePreviousImplementationTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");

    private static final Value FIVE = Value.text("5");
    private static final Value SIX = Value.text("6");
    private static final Value ZERO = Value.text("0");

    private sealed interface Term {
        record Leaf(String show, AdmissibleValues<String> held,
                    ProductHullReference<String> before) implements Term {}
        record Meet(Term left, Term right) implements Term {}
        record Join(Term left, Term right) implements Term {}
        /** Shown to admit nothing from outside, which is the one bottom no position is at fault
         *  for. */
        record Nothing(Term of) implements Term {}
    }

    private static Term leaf(String show, AdmissibleValues<String> held,
                             ProductHullReference<String> before) {
        return new Term.Leaf(show, held, before);
    }

    /**
     * The readings a clause can be read into, one of each shape that answers differently.
     *
     * <p>A position narrowed to one value and to all but one, a position left nothing, a rule this
     * could not read that names one position and one that names two, and a rule naming none — which
     * is the one a choice has nothing to spoil with, and the one a reading of it can only be told
     * from the others by what it drops.
     */
    private static List<Term> leaves() {
        return List.of(
                leaf("top", AdmissibleValues.top(), ProductHullReference.top()),
                leaf("a=5", AdmissibleValues.at("a", ValueSet.just(FIVE)),
                        ProductHullReference.at("a", ValueSet.just(FIVE))),
                leaf("a=6", AdmissibleValues.at("a", ValueSet.just(SIX)),
                        ProductHullReference.at("a", ValueSet.just(SIX))),
                leaf("a/=5", AdmissibleValues.at("a", ValueSet.allBut(FIVE)),
                        ProductHullReference.at("a", ValueSet.allBut(FIVE))),
                leaf("a=none", AdmissibleValues.at("a", ValueSet.NONE),
                        ProductHullReference.at("a", ValueSet.NONE)),
                leaf("b=0", AdmissibleValues.at("b", ValueSet.just(ZERO)),
                        ProductHullReference.at("b", ValueSet.just(ZERO))),
                leaf("?a", AdmissibleValues.unreadable(Set.of("a"), UnreadReason.FORM_NOT_READ),
                        ProductHullReference.unreadable(Set.of("a"), UnreadReason.FORM_NOT_READ)),
                leaf("?ab", AdmissibleValues.unreadable(Set.of("a", "b"),
                        UnreadReason.RELATES_TWO_POSITIONS),
                        ProductHullReference.unreadable(Set.of("a", "b"),
                                UnreadReason.RELATES_TWO_POSITIONS)),
                leaf("?", AdmissibleValues.unreadable(Set.of(), UnreadReason.FORM_NOT_READ),
                        ProductHullReference.unreadable(Set.of(), UnreadReason.FORM_NOT_READ)));
    }

    private static AdmissibleValues<String> held(Term term) {
        return switch (term) {
            case Term.Leaf it -> it.held();
            case Term.Meet it -> held(it.left()).meet(held(it.right()));
            case Term.Join it -> held(it.left()).join(held(it.right()));
            case Term.Nothing it -> held(it.of()).leavingNothing();
        };
    }

    private static ProductHullReference<String> before(Term term) {
        return switch (term) {
            case Term.Leaf it -> it.before();
            case Term.Meet it -> before(it.left()).meet(before(it.right()));
            case Term.Join it -> before(it.left()).join(before(it.right()));
            case Term.Nothing it -> before(it.of()).leavingNothing();
        };
    }

    private static String show(Term term) {
        return switch (term) {
            case Term.Leaf it -> it.show();
            case Term.Meet it -> "(" + show(it.left()) + " && " + show(it.right()) + ")";
            case Term.Join it -> "(" + show(it.left()) + " || " + show(it.right()) + ")";
            case Term.Nothing it -> "nothing(" + show(it.of()) + ")";
        };
    }

    /** Every term of one more connective than {@code these}, over the leaves. */
    private static List<Term> grown(List<Term> these, List<Term> leaves) {
        List<Term> out = new ArrayList<>();
        for (Term each : these) {
            out.add(new Term.Nothing(each));
            for (Term leaf : leaves) {
                out.add(new Term.Meet(each, leaf));
                out.add(new Term.Meet(leaf, each));
                out.add(new Term.Join(each, leaf));
                out.add(new Term.Join(leaf, each));
            }
        }
        return out;
    }

    private static void sameAnswers(Term term) {
        AdmissibleValues<String> now = held(term);
        ProductHullReference<String> was = before(term);
        String about = show(term);

        assertEquals(was.isBottom(), now.isBottom(), about + ": whether anything satisfies it");
        assertEquals(was.dropped(), now.dropped(), about + ": whether a rule went unread");
        assertEquals(was.relationExact(), now.relationExact(), about + ": the relation's promise");
        for (String position : POSITIONS) {
            assertEquals(was.at(position), now.at(position), about + ": what " + position + " may hold");
            assertEquals(was.guaranteedAt(position), now.guaranteedAt(position),
                    about + ": what " + position + " is guaranteed");
            assertEquals(was.speaksFor(position), now.speaksFor(position),
                    about + ": whether it speaks for " + position);
            assertEquals(was.whyUnread(position), now.whyUnread(position),
                    about + ": what stopped it at " + position);
            assertEquals(was.projectionExactAt(position), now.projectionExactAt(position),
                    about + ": the promise about " + position);
        }
    }

    @Test
    void everyReadingOfOneConnectiveIsAnsweredAlike() {
        List<Term> leaves = leaves();
        leaves.forEach(AReadingHeldAsOneBoxIsThePreviousImplementationTest::sameAnswers);
        grown(leaves, leaves).forEach(
                AReadingHeldAsOneBoxIsThePreviousImplementationTest::sameAnswers);
    }

    @Test
    void andSoIsEveryReadingOfTwo() {
        List<Term> leaves = leaves();
        List<Term> deeper = grown(grown(leaves, leaves), leaves);

        assertTrue(deeper.size() > 5000, "the shapes are enumerated and not sampled: " + deeper.size());
        deeper.forEach(AReadingHeldAsOneBoxIsThePreviousImplementationTest::sameAnswers);
    }
}
