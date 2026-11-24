package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.BlockReason;
import souther.compiler.regex.PatternPlan;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What kept something from an offer is said under the allowance it was refused under, and a thing
 * no limit refused is not given one.
 *
 * <p>The strings made for a body's demand are met with what a position admits, and a position whose
 * machine could not be made says so in the offer it hands back. What the search that asked reports
 * is that refusal: the limit and the allowance it was made under, which differ between a machine
 * built for one pattern and everything a question builds. A refusal reported under the allowance of
 * the question that happened to ask would send a reader to raise a figure that stopped nothing.
 *
 * <p>Held over the offer rather than through a compile, as the allowance spent is
 * ({@link AnAllowanceSpentIsNotOneRulesDoingTest}).
 */
class WhatARefusedOfferSaysAboutTheAllowanceIsKeptWithItTest {

    private static PartId<RuleRef.Invariant> aPart() {
        return new PartId<>(new RuleRef.Invariant(new Clause.Ref(new Clause.Id(
                TypeSymbols.declared(new TypeKey("example.kept", "Code")), 0),
                Optional.of(new ClauseName("shape")))), 0);
    }

    private static StringOfferShortfall.Subject.ARule aRule() {
        return new StringOfferShortfall.Subject.ARule(aPart());
    }

    /** One pattern's machine is refused under the allowance one pattern has. */
    @Test
    void aPatternsMachineIsRefusedUnderTheAllowanceOfOnePattern() {
        StringOfferShortfall offer = StringOfferShortfall.of(
                StringOfferShortfall.NotOffered.patternNotBuilt(aRule(),
                        Meter.Stopped.ONE_MACHINE));

        assertEquals(Optional.of(new PatternPlan.Refused(
                        PatternPlan.Budget.OF_A_PATTERN_FOR_A_WITNESS, Meter.Stopped.ONE_MACHINE)),
                offer.refusedBy());
    }

    /** And what composing a value built in all is refused under the allowance of a witness. */
    @Test
    void whatComposingAValueBuiltIsRefusedUnderTheAllowanceOfAWitness() {
        StringOfferShortfall offer = StringOfferShortfall.of(new StringOfferShortfall.NotOffered(
                new StringOfferShortfall.Subject.ComposingAValue(),
                new StringOfferShortfall.Why.TooCostly(Meter.Stopped.THE_ANSWER)));

        assertEquals(Optional.of(new PatternPlan.Refused(PatternPlan.Budget.OF_A_WITNESS,
                Meter.Stopped.THE_ANSWER)), offer.refusedBy());
    }

    /**
     * A rule this compiler did not read kept something from the offer, and no limit refused it:
     * there is no figure to name, and none is made up.
     */
    @Test
    void aRuleThatWasNotReadWasRefusedByNoLimit() {
        StringOfferShortfall offer = StringOfferShortfall.of(
                StringOfferShortfall.NotOffered.ofARuleNotRead(aPart(),
                        new BlockReason.UnreadValueRule()));

        assertEquals(Optional.empty(), offer.refusedBy());
        assertEquals(Optional.empty(), StringOfferShortfall.NONE.refusedBy());
    }
}
