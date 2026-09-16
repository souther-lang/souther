package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.crossing.DelegatedEqualityIsRepresentedByWhatItStandsFor;
import souther.compiler.crossing.DelegatedEqualityIsTheCrossingAnswer;
import souther.compiler.types.BinOp;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every form whose whole comparison is left to an equality says, once, that this is right.
 *
 * <p>The comparison reads a form by taking it apart until it has nothing of its own to say about
 * one, and then hands the two sides over to be compared as written values. Where that equality
 * answers what taking the form apart would have answered there is nothing to say; where it answers
 * something else, two builds that have moved are reported as agreeing and nothing fails. Which of
 * the two it is cannot be read off the rule that chose to hand the form over — that rule holds for
 * every form it hands over, including the wrong one — so it is said, and this is what refuses a
 * form that says nothing.
 *
 * <p>Two ways of saying it, because two kinds of form are handed over. A form written here says it
 * for itself, beside what it is a claim about. A form the platform declares cannot say anything,
 * and what is claimed about one is claimed by the comparison that hands it over.
 *
 * <p><b>Once and not at least once.</b> A form saying both has two authorities for one claim with
 * nothing to say which governs, which is the same as nobody having said it — and is how a form
 * written here would come to be covered by a rule about the platform's types, or the other way
 * round.
 *
 * <p>Over what a crossing can reach and not over what a run met. A form no model here happens to
 * write is one an author writes tomorrow, and it would arrive accounted for by nobody.
 */
class EveryFormHandedToADelegatedEqualityIsAccountedForTest {

    @Test
    void everyFormHandedToADelegatedEqualitySaysExactlyOneAccountOfIt() {
        List<String> saidOtherThanOnce = new ArrayList<>(new TreeSet<>(
                FormsACrossingCanReach.handedToADelegatedEquality().stream()
                        .filter(form -> accountsGiven(form) != 1)
                        .map(form -> form.getName() + " says " + accountsGiven(form) + " of them")
                        .toList()));

        assertEquals(List.of(), saidOtherThanOnce,
                "the whole comparison of these is an equality this class did not write, and each is"
                        + " to say once that the equality answers what reading the form would have."
                        + " Saying none leaves two builds held together by a rule nobody chose, and"
                        + " saying both is two authorities for one claim");
    }

    /**
     * The population, as a control rather than as where the answer comes from.
     *
     * <p>Written down so that a form joining or leaving it is read by somebody. What is asked of
     * each of them is asked above, off the census and off the comparison's own answers; this says
     * which forms that came to, on the day it was last looked at.
     *
     * <p>{@code Integer} is the one worth naming. Nothing any model in this repository writes has
     * reached it — it is what a tuple holds its position in, and no crossing here has met one — and
     * it is in the population all the same. A population taken from what runs happened to reach
     * would have left it out, and the account for it would be owed by nobody until an author wrote
     * the first tuple.
     */
    @Test
    void andThoseAreTheFormsHandedOver() {
        List<String> handedOver = new ArrayList<>(new TreeSet<>(
                FormsACrossingCanReach.handedToADelegatedEquality().stream()
                        .map(Class::getName).toList()));

        assertEquals(List.of(
                        "java.lang.Boolean",
                        "java.lang.Integer",
                        "java.lang.Long",
                        "java.lang.String",
                        "java.math.BigDecimal",
                        "souther.compiler.ast.Hir$Fields",
                        "souther.compiler.types.BinOp",
                        "souther.compiler.types.LanguageCaseId",
                        "souther.compiler.types.Type$Prim",
                        "souther.compiler.types.TypeSymbol$AtModule"),
                handedOver,
                "a form added here is one more whose comparison is an equality, and one removed is"
                        + " one the comparison now reads for itself");
    }

    /**
     * The control for the first way of getting it wrong: a form nobody spoke for is not passed
     * over.
     *
     * <p>Without it a sweep whose counting answered one for everything would report nothing and say
     * nothing.
     */
    @Test
    void andTheSweepWouldSeeAFormThatSaysNeither() {
        assertEquals(0, accountsGiven(SaysNeither.class),
                "a form handed to an equality with nothing said about it is not passed over");
    }

    /**
     * The control for the second: nothing is spoken for twice.
     *
     * <p>Said of the forms there are rather than of a stand-in. A form that says both cannot be
     * written here to be counted — what the comparison speaks for is a written list of forms this
     * repository does not declare, and a form declared here can be added to that list and to
     * nothing else. So what is held is the list itself: it names forms that cannot say anything for
     * themselves, and a form that could say something is one the list has taken authority over.
     */
    @Test
    void andNothingIsSpokenForByBothItsWriterAndThisComparison() {
        List<String> spokenForTwice = new ArrayList<>(new TreeSet<>(
                DeclarationAgreement.saidByThisComparison().stream()
                        .filter(DelegatedEqualityIsTheCrossingAnswer.class::isAssignableFrom)
                        .map(Class::getName).toList()));

        assertEquals(List.of(), spokenForTwice,
                "this comparison speaks for these because they cannot speak for themselves, and one"
                        + " that does has two authorities for one claim with nothing to say which"
                        + " governs");
    }

    /**
     * And the two kinds of account are told apart, with the stronger one implying the weaker.
     *
     * <p>A form naming what its equality is over has said the weaker thing too, and counting it
     * twice would make every one of them a form two writers spoke for.
     */
    @Test
    void andNamingARepresentationIsOneAccountAndNotTwo() {
        assertEquals(1, accountsGiven(TypeSymbol.AtModule.class),
                "which declaration this is, named as the address it holds");
        assertEquals(1, accountsGiven(Type.Prim.class),
                "one of a closed set of cases, with nothing inside to name");
        assertEquals(1, accountsGiven(BigDecimal.class),
                "and a written number, which this comparison speaks for because the class cannot");
    }

    /** Stands for a form handed to an equality that nobody has decided about. */
    private record SaysNeither(String what) {}

    /**
     * How many accounts {@code form} has of the equality its comparison is left to.
     *
     * <p>Counted and not asked whether there is one. The stronger claim is the weaker one said more
     * precisely rather than a second claim, so it counts once; a form spoken for here and by this
     * comparison counts twice, which is the one this is looking for.
     */
    private static int accountsGiven(Class<?> form) {
        int given = 0;
        if (DelegatedEqualityIsTheCrossingAnswer.class.isAssignableFrom(form)) {
            given++;
        }
        if (DeclarationAgreement.saidByThisComparison().contains(form)) {
            given++;
        }
        return given;
    }

    /** Held so the population above is read as the forms it names rather than as words. */
    @Test
    void andTheFormsNamedAreTheOnesMeant() {
        assertEquals(Hir.Fields.class.getName(), "souther.compiler.ast.Hir$Fields");
        assertEquals(BinOp.class.getName(), "souther.compiler.types.BinOp");
        assertEquals(LanguageCaseId.class.getName(), "souther.compiler.types.LanguageCaseId");
    }

    /** The stronger account is what {@code AtModule} says, and the weaker is not enough for it. */
    @Test
    void andAFormWithSomethingInsideNamesWhatItsEqualityIsOver() {
        assertEquals(true,
                DelegatedEqualityIsRepresentedByWhatItStandsFor.class
                        .isAssignableFrom(TypeSymbol.AtModule.class),
                "it holds an address, so what its equality is over is something it can name");
        assertEquals(false,
                DelegatedEqualityIsRepresentedByWhatItStandsFor.class
                        .isAssignableFrom(Type.Prim.class),
                "and one of a closed set of cases has nothing to name, so naming one would be"
                        + " inventing something for a check to be held to");
    }
}
