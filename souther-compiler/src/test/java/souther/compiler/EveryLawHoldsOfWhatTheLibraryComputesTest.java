package souther.compiler;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every law the library's operations are settled by holds of what the library computes, over
 * values chosen at the edges each law turns on.
 *
 * <p>A law is an equivalence a reader carries a statement across, and the binder holds it to the
 * signature only: that each argument it names is there and has the side it is observed on. Whether
 * the answer really comes out that way is what the operation's definition says, and this asks the
 * definition. What is checked is written from the law itself — the observation of the answer on one
 * side, the law's proposition over the same arguments on the other — so no law is declared or
 * derived without being run, and none is run in words of its own ({@link WhatTheLibraryComputes}).
 */
class EveryLawHoldsOfWhatTheLibraryComputesTest {

    /** Each observation's laws on their own, so what one case compiles is that observation's. */
    @ParameterizedTest
    @EnumSource(OperationLaw.Observed.class)
    void everyLawHoldsWhereItsOperationAnswers(OperationLaw.Observed of) throws Exception {
        List<WhatTheLibraryComputes.Statement> laws = new ArrayList<>();
        DefaultBoundOperationFacts.get().settled().forEach((operation, settled) ->
                settled.forEach((observed, settling) -> {
                    if (observed == of && settling instanceof BoundOperationFacts.Settled.ByALaw(
                            var law, var _)) {
                        laws.add(WhatTheLibraryComputes.ofALaw(
                                (ValueName.Stdlib.Operation) operation, law));
                    }
                }));
        WhatTheLibraryComputes.Held held = WhatTheLibraryComputes.run(laws);
        assertEquals(List.of(), held.broken());
        assertEquals(List.of(), held.neverAnswered(), "a law held to no call that answered");
    }
}
