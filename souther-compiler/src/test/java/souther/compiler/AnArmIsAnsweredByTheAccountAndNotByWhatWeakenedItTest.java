package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.ArmSummary;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What became of an arm is the account's answer, and there is no way round it to the reasons.
 *
 * <p>Checked against the shape of the API rather than against an answer, for the reason
 * {@code NoPublicWayToTurnASpellingIntoATypeIdentityTest} gives: the rule had been written down
 * before and was broken all the same. A sentence is kept by whoever reads it; a signature is kept by
 * everyone.
 *
 * <p>Written outside {@code souther.compiler.query} on purpose. What it says is what a reader
 * outside the package can reach, and a check making that claim from inside would be standing where
 * the claim does not apply.
 *
 * <p><b>What the rule is.</b> Every question about the arms is answered from the account, which
 * decided each arm's state from what was observed. Nothing answers one by reading what weakened the
 * measurement: those reasons are about particular arms and about the set of them, and a reader
 * sorting them by their kind is deciding what an arm came to out of facts that were never about one
 * arm. That is what the accessors this replaced did — one answered which arms nothing reached and
 * withheld the answer whenever any reason at all stood, one recovered the contradicted probes from
 * the reasons and one recovered the forks — so an arm the rows certainly do not reach went unnamed
 * because a fork elsewhere in the body could not be told apart.
 */
class AnArmIsAnsweredByTheAccountAndNotByWhatWeakenedItTest {

    /**
     * The measure has three questions and they are the three a consumer needs: whether there is an
     * account, what it is, and what stopped there being one.
     *
     * <p>Whitelisted rather than counted. A method added here is not a mistake by itself — it is a
     * claim that something about the arms cannot be asked of the account, and that claim is worth
     * making out loud in this list before it is made in a surface.
     */
    @Test
    void theMeasureAnswersWithTheAccountAndNothingBeside() {
        assertEquals(List.of("applicable", "arms", "measured"),
                publicNamesOf(Adequacy.BranchEvidence.class),
                "a question about the arms answered here rather than by the account is a second"
                        + " reading of the same measurement");
    }

    /**
     * And no accessor hands the account back under a name meaning "you may ask it".
     *
     * <p>The shape this replaced. {@code unreached()} answered "may the claim be made" by returning
     * the arms or nothing, so whether there is an answer and what it is were two calls with a
     * protocol between them, and every surface kept that protocol on its own — the report read the
     * presence of the answer as "every row was read" and wrote that sentence whatever the reason
     * had been. A method of this shape coming back is the protocol coming back.
     */
    @Test
    void noAccessorHandsTheAccountOutForACallerToDrawAClaimFrom() {
        assertEquals(List.of(), optionalReturnsOf(Adequacy.BranchEvidence.class),
                "a measure that hands its value over under a name meaning `you may ask it` is the"
                        + " two-call protocol this removed");
        assertEquals(List.of(), optionalReturnsOf(ArmSummary.class),
                "and the account does not grow one either");
    }

    private static List<String> publicNamesOf(Class<?> type) {
        return java.util.Arrays.stream(type.getDeclaredMethods())
                .filter(each -> Modifier.isPublic(each.getModifiers()))
                // What a reader of a measure can ask it. The static ones make one, and making a
                // measure is not a question about the arms it holds.
                .filter(each -> !Modifier.isStatic(each.getModifiers()))
                .map(Method::getName)
                .distinct()
                // What every record has. The three of these say nothing about the arms.
                .filter(name -> !List.of("equals", "hashCode", "toString").contains(name))
                .sorted().toList();
    }

    private static List<String> optionalReturnsOf(Class<?> type) {
        return java.util.Arrays.stream(type.getDeclaredMethods())
                .filter(each -> Modifier.isPublic(each.getModifiers()))
                .filter(each -> each.getReturnType() == Optional.class)
                .map(Method::getName).sorted().toList();
    }
}
