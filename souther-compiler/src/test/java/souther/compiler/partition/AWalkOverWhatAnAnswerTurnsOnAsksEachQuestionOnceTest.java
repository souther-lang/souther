package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.KeptCalls;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk over what a fork's answer turns on asks each question once.
 *
 * <p>What stops it. The walk follows what the library says an answer turns on and follows a name to
 * what it stands for, and what a name stands for is not this walk's to bound: a reading that
 * answered a closure with something the walk is already inside would go round for ever. So a
 * question already asked is one already answered.
 *
 * <p>Held against a reading that does go round, because nothing else can hold it. The models this
 * compiler has do not write one — a {@code let} cannot read the name it binds — so a walk over them
 * says nothing about whether the walk would stop if one arrived, and the alternative to stopping is
 * a compile that never finishes.
 *
 * <p>And it is the question that is asked once and not the object standing for it. A question is
 * built where it is asked, so two of them about one expression are two objects and one question —
 * which is what {@code Asked} says, and what says it holds is that whatever collects them asks it.
 */
class AWalkOverWhatAnAnswerTurnsOnAsksEachQuestionOnceTest {

    private static final ValueName.Stdlib.Operation ANY =
            new ValueName.Stdlib.Operation("List", "any");

    private static final SourcePos POS = new SourcePos(1, 1);

    /** {@code List.any} over a closure and a list, which is a truth its closure decides. */
    private static Core.PreservedCall anyOverAClosure() {
        return KeptCalls.to(ANY, POS);
    }

    /**
     * A closure that answers with the very call it is handed to.
     *
     * <p>The walk asks what the closure comes to, gets the call back, and asks the call what it
     * turns on again. Told each question once it says the rule is not among them; told nothing, it
     * asks for ever.
     */
    @Test
    @Timeout(10)
    void aClosureThatAnswersWithWhatItWasHandedToIsAskedOnce() {
        Core.PreservedCall call = anyOverAClosure();
        assertEquals(List.of(call),
                WhatAForkTests.partsOfTheAnswer(call, through(e -> e == call ? e : call)),
                "a reading that leads back to the question it came from answers it once");
    }

    /**
     * An operation applied as a call to what its name reached is read as the same operation it is
     * standing as itself: every element meeting what always holds turns on nothing, and some
     * element meeting it turns on whether the list holds anything, which is the application.
     */
    @Test
    void anOperationCalledByWhatItsNameReachedIsReadAsTheOperation() {
        Core.Call every = calling(ValueName.Stdlib.operation("List", "all"));
        Core.Call some = calling(ValueName.Stdlib.operation("List", "any"));
        assertEquals(List.of(), WhatAForkTests.partsOfTheAnswer(every, through(e -> e)),
                "true whatever the list is");
        assertEquals(List.of(some), WhatAForkTests.partsOfTheAnswer(some, through(e -> e)),
                "whether the list holds anything");
    }

    /** {@code operation} over a list and a closure that always holds, called by what its name
     *  reached. */
    private static Core.Call calling(ValueName.Stdlib.Operation operation) {
        BindingOwner owner = new BindingOwner.OfValue("demo", "walk");
        Core.Block holds = new Core.Block(
                List.of(new Core.Binder("e", new BindingId(owner, 0))), List.of(Type.INT),
                new Core.Bool(true, Type.BOOL, POS), POS);
        Core.Read list = new Core.Read("xs", new BindingId(owner, 1), Type.list(Type.INT), POS);
        return new Core.Call(new Core.Reached.OfDeclaration(new ReachName.OfLibrary(operation)),
                List.of(holds, list), ConstructOccurrence.unwritten(),
                Core.CallSettlement.None.INSTANCE, Type.BOOL, POS);
    }

    /** Names that stand for what {@code denotes} says, none of them for a written value. */
    private static WhatNamesStandFor through(UnaryOperator<Core> denotes) {
        return new WhatNamesStandFor() {
            @Override
            public Core denotes(Core e) {
                return denotes.apply(e);
            }

            @Override
            public boolean writtenOut(Core e) {
                return false;
            }

            @Override
            public Optional<Boolean> everyRowBrings(Core comparison) {
                return Optional.empty();
            }
        };
    }

    /**
     * And the walk still reaches what the closure decides where the reading is an ordinary one.
     *
     * <p>The negative control for the one above: a stop that fired on the first question asked
     * would make every fork turn on nothing, and both tests would pass.
     */
    @Test
    void aClosureIsStillReadForWhatItDecides() {
        Core.PreservedCall call = anyOverAClosure();
        assertEquals(List.of(call.args().get(0)), WhatAForkTests.partsOfTheAnswer(call, through(e -> e)),
                "what the answer turns on is reached");
    }
}
