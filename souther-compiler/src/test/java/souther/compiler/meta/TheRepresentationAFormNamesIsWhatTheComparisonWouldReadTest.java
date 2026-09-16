package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.crossing.DelegatedEqualityIsRepresentedByWhatItStandsFor;
import souther.compiler.crossing.DelegatedEqualityIsTheCrossingAnswer;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeSymbol;

import java.lang.reflect.Method;
import java.lang.reflect.Type;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form that names what its equality is over is held to the comparison reading the same thing.
 *
 * <p>The account a form gives of the equality its comparison is left to is its writer's word, and a
 * word is all it is while nothing can come out false. A form that names the one value its equality
 * is over has said something more than a word: what it named can be walked by the rules this
 * comparison uses everywhere else, and if that walk meets a part the comparison passes over — or
 * one it reads by an answer rather than by what the part holds — then the equality reads something
 * the comparison does not, and the account is wrong.
 *
 * <p><b>Which is the thing the reading beside this one cannot do.</b> Asked whether a form's
 * equality answers what this comparison would, and answering from the rule that chose to hand the
 * form to its equality, the answer is that rule restated and holds for every form it hands over.
 * Asked of the representation the form itself named, the answer comes from somewhere the mode did
 * not.
 *
 * <p>Over declared types and not over values. What a part may hold is a question about the form,
 * and an identity these are made by is closed to whoever is not the world that hands one out — so a
 * reading over values would be a reading over the ones a fixture could reach.
 */
class TheRepresentationAFormNamesIsWhatTheComparisonWouldReadTest {

    /**
     * Every form naming a representation is read the same way by the comparison.
     *
     * <p>The population is the forms a crossing can reach that say the stronger of the two
     * accounts. There is one today, and how many there are is not what this is about: what is being
     * held is that the account is the kind of claim that can be wrong, and the control below is
     * what says this reading would notice.
     */
    @Test
    void everyFormNamingARepresentationIsReadTheSameWayByTheComparison() {
        List<String> readingMore = new ArrayList<>(new TreeSet<>(
                FormsACrossingCanReach.handedToADelegatedEquality().stream()
                        .filter(DelegatedEqualityIsRepresentedByWhatItStandsFor.class
                                ::isAssignableFrom)
                        .filter(form -> !whatItNamesIsReadTheSameWay(form))
                        .map(Class::getName).toList()));

        assertEquals(List.of(), readingMore,
                "these say their comparison may be left to an equality because that equality is"
                        + " over the value they name, and the comparison does not read that value"
                        + " the way the equality does — so two builds are held together over"
                        + " something this comparison decided it cannot see");
    }

    /**
     * The positive control: the one form in the population passes, and for a reason that can be
     * followed.
     */
    @Test
    void andTheOneFormInThePopulationIsReadTheSameWay() {
        assertTrue(DelegatedEqualityIsRepresentedByWhatItStandsFor.class
                        .isAssignableFrom(TypeSymbol.AtModule.class),
                "which declaration something is names the address it holds");
        assertTrue(whatItNamesIsReadTheSameWay(TypeSymbol.AtModule.class),
                "and an address is a pair of words, each of which this comparison reads as the"
                        + " word it is");
    }

    /**
     * The negative control: this reading answers no, and answers it about a real value.
     *
     * <p><b>Not a form a crossing reaches.</b> An expansion of a helper owns bindings, and what a
     * published declaration is read back as holds none of them — the census says so and a rule over
     * who may build one holds it. So nothing here is a claim about the comparison as it stands.
     *
     * <p>What it is for is that this reading can come out false at all, and it is worth more than a
     * fixture written to fail: an expansion names the parts its equality is over, and one of them
     * is the application it was expanded at, which is a record of how this compile ran and is a
     * thing the comparison passes over on purpose. An account claiming that equality would be
     * claiming a comparison over something no crossing can see, and this says no to it.
     */
    @Test
    void andTheReadingSaysNoToAnEqualityOverWhatTheComparisonPassesOver() {
        assertFalse(FormsACrossingCanReach.handedToADelegatedEquality()
                        .contains(BindingOwner.Expansion.class),
                "no crossing reaches one, so nothing here is about what the comparison does today");
        assertTrue(whatStopsIt(BindingOwner.Expansion.class).contains(
                        "souther.compiler.types.ApplicationOrigin$Written is passed over by the"
                                + " comparison"),
                "and it says no for the reason it is here to show: what it names holds the"
                        + " application it was expanded at, which is a record of how this compile"
                        + " ran and is a thing the comparison passes over on purpose — so an"
                        + " equality over what it names reads what no crossing can see");
    }

    /**
     * Whether the comparison reads what {@code form} names the way an equality over it would.
     *
     * <p>The comparison's own answers, in the order it takes them. A part it passes over is one an
     * equality reading it reads more than the comparison; a part it reads by an answer settled
     * beside the spelling is one it reads differently; a part it takes apart is followed; and a
     * part it hands to an equality of its own is right exactly where somebody has said so, which is
     * the account this is checking one step down.
     */
    private static boolean whatItNamesIsReadTheSameWay(Class<?> form) {
        return whatStopsIt(form).isEmpty();
    }

    /**
     * What in the representation {@code form} names the comparison does not read the way an
     * equality over it would, and why — empty where there is nothing.
     *
     * <p>Answered with what stopped it rather than with no, so that a form failing this is read by
     * whoever has to decide about it, and so that a control saying no says no for the reason it
     * claims to.
     */
    private static List<String> whatStopsIt(Class<?> form) {
        List<String> stopping = new ArrayList<>();
        Deque<Type> todo = new ArrayDeque<>();
        todo.add(namedBy(form));
        Set<Class<?>> seen = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            for (Class<?> declared : TypesAPartIsDeclaredToHold.named(todo.removeFirst())) {
                Class<?> held = FormsACrossingCanReach.asItArrives(declared);
                if (!seen.add(held)) {
                    continue;
                }
                if (DeclarationAgreement.erases(held)) {
                    stopping.add(held.getName() + " is passed over by the comparison");
                    continue;
                }
                if (DeclarationAgreement.readByTheAnswerBesideItsSpelling(held)
                        || held == BindingId.class) {
                    stopping.add(held.getName() + " is read by the answer beside its spelling");
                    continue;
                }
                if (held.isSealed()) {
                    for (Class<?> permitted : held.getPermittedSubclasses()) {
                        todo.addLast(permitted);
                    }
                    continue;
                }
                if (StructuralParts.areHandedOver(held)) {
                    for (StructuralParts.Part part : StructuralParts.of(held)) {
                        todo.addLast(part.held());
                    }
                    continue;
                }
                if (!DelegatedEqualityIsTheCrossingAnswer.class.isAssignableFrom(held)
                        && !DeclarationAgreement.saidByThisComparison().contains(held)) {
                    stopping.add(held.getName() + " is handed to an equality nobody speaks for");
                }
            }
        }
        return stopping;
    }

    /** The representation {@code form} names, as the type it is declared to answer with. */
    private static Type namedBy(Class<?> form) {
        try {
            Method names = form.getMethod("standsFor");
            return names.getGenericReturnType();
        } catch (NoSuchMethodException e) {
            throw new IllegalStateException(form.getName() + " says its equality is over what it"
                    + " names and names nothing", e);
        }
    }
}
