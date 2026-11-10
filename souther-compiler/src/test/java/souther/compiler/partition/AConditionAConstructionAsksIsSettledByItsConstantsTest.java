package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatAConstructionAsks;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.ConstructionAsk.Requirement;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a construction asks of a run is a condition of one of five kinds — nothing, no run, one
 * form standing some way to a number, every one of several, and one of several — and a part that is
 * only a constant settles what it is a part of. A number that nothing holds apart is neither
 * nothing asked nor a run that stops: the lesser of a number below nought and any other is at
 * nought or above by no run, and the greater of it and another is at nought or above where the
 * other is.
 */
class AConditionAConstructionAsksIsSettledByItsConstantsTest {

    /** What the way holds, which is a condition nothing says anything else of. */
    private static final Proposition HELD = new Proposition.Always(true);

    private static final Proposition NOT_HELD = new Proposition.Always(false);

    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    private static final WhatAConstructionAsks.Bearing EVERY_RULE =
            new WhatAConstructionAsks.OnEveryRule();

    private static Requirement ask(String form, Proposition read) {
        return new Requirement.Is(new WhatAConstructionAsks.Is(form, Rel.GE, "0"), read);
    }

    private static final Requirement X = ask("x", NOT_HELD);

    private static final Requirement Y = ask("y", NOT_HELD);

    @Test
    void bothIsNoRunWhereEitherIsAndWhatTheOtherAsksWhereOneAsksNothing() {
        assertEquals(Requirement.NEVER, Requirement.and(Requirement.NEVER, X));
        assertEquals(Requirement.NEVER, Requirement.and(X, Requirement.NEVER));
        assertEquals(Requirement.NEVER, Requirement.and(Requirement.NEVER, Requirement.ALWAYS));
        assertEquals(X, Requirement.and(Requirement.ALWAYS, X));
        assertEquals(X, Requirement.and(X, Requirement.ALWAYS));
        assertEquals(Requirement.ALWAYS, Requirement.and(Requirement.ALWAYS, Requirement.ALWAYS));
        assertEquals(new Requirement.AllOf(List.of(X, Y)), Requirement.and(X, Y));
    }

    /** A part no run meets leaves the other alternative as it is, and is not nothing asked. */
    @Test
    void eitherIsNothingAskedWhereEitherAsksNothingAndWhatTheOtherAsksWhereOneIsMetByNoRun() {
        assertEquals(Requirement.ALWAYS, Requirement.or(Requirement.ALWAYS, X));
        assertEquals(Requirement.ALWAYS, Requirement.or(X, Requirement.ALWAYS));
        assertEquals(Requirement.ALWAYS, Requirement.or(Requirement.NEVER, Requirement.ALWAYS));
        assertEquals(X, Requirement.or(Requirement.NEVER, X));
        assertEquals(X, Requirement.or(X, Requirement.NEVER));
        assertEquals(Requirement.NEVER, Requirement.or(Requirement.NEVER, Requirement.NEVER));
        assertEquals(new Requirement.OneOf(List.of(X, Y)), Requirement.or(X, Y));
    }

    @Test
    void severalOfOneKindAreOneListAndNotNested() {
        Requirement z = ask("z", NOT_HELD);
        assertEquals(new Requirement.AllOf(List.of(X, Y, z)),
                Requirement.and(Requirement.and(X, Y), z));
        assertEquals(new Requirement.OneOf(List.of(X, Y, z)),
                Requirement.or(X, Requirement.or(Y, z)));
    }

    /** What the way holds is left out part by part, and a part left out of a disjunction that
     *  the way holds whole makes the disjunction nothing. */
    @Test
    void whatTheWayHoldsIsLeftOutOfWhatIsAskedPartByPart() {
        Requirement held = ask("w", HELD);
        assertEquals(Requirement.ALWAYS, held.leavingOut(HELD::equals));
        assertEquals(Y, Requirement.and(held, Y).leavingOut(HELD::equals));
        assertEquals(Requirement.ALWAYS, Requirement.or(held, Y).leavingOut(HELD::equals));
        assertEquals(new Requirement.OneOf(List.of(X, Y)),
                Requirement.or(X, Y).leavingOut(HELD::equals));
        assertEquals(Requirement.NEVER, Requirement.NEVER.leavingOut(HELD::equals));
    }

    @Test
    void whatIsToldIsWhatIsLeftAndNothingWhereNothingIs() {
        Requirement both = Requirement.and(ask("w", HELD), Y);
        ConstructionAsk one = new ConstructionAsk("Held", NOWHERE, EVERY_RULE, both);
        assertEquals(Optional.of(new WhatAConstructionAsks.Is("y", Rel.GE, "0")),
                one.toldOf(HELD::equals).map(WhatAConstructionAsks::asks));
        assertEquals(Optional.empty(), new ConstructionAsk("Held", NOWHERE, EVERY_RULE,
                ask("w", HELD)).toldOf(HELD::equals));
        assertEquals(Optional.of(new WhatAConstructionAsks.Never()),
                new ConstructionAsk("Held", NOWHERE, EVERY_RULE, Requirement.NEVER)
                        .toldOf(HELD::equals).map(WhatAConstructionAsks::asks));
    }
}
