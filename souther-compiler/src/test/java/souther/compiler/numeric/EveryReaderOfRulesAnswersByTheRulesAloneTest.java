package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesReaders.Reader;
import souther.compiler.numeric.RulesReaders.Tally;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.numeric.RulesAsWritten.OVER_THREE;
import static souther.compiler.numeric.RulesAsWritten.everyOrder;
import static souther.compiler.numeric.RulesAsWritten.relationsIn;

/**
 * What every reader of a set of rules says is what the rules say, over the systems chosen for the
 * steps the readers take.
 *
 * <p>The readers are the closed state, the reduction and the difference bounds
 * ({@link RulesReaders#READERS}), and each is held to the same three claims: the same answer in
 * every order the rules have, the same answer however often each was said, and no point the rules
 * admit left outside it. The systems are those of {@link RulesAsWritten#OVER_THREE}, each written
 * for a step the closure or the reduction takes or hands on, and the ones the difference bounds
 * have a step for ({@link WhatTheDifferenceBoundsSayIsWhatThePointsSayTest#SYSTEMS}). Two rules
 * bounding one thing are in them, so a reader letting the later one win, or the one said between,
 * answers differently in some order — which is why each system is given in every order its rules
 * have.
 *
 * <p>{@code EveryReaderOfDrawnRulesAnswersByTheRulesAloneTest} asks the same of rules drawn at
 * random, which reaches combinations no chosen system names.
 */
class EveryReaderOfRulesAnswersByTheRulesAloneTest {

    private static List<List<Written>> systems() {
        List<List<Written>> out = new ArrayList<>(OVER_THREE);
        out.addAll(WhatTheDifferenceBoundsSayIsWhatThePointsSayTest.SYSTEMS);
        return out;
    }

    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        for (Reader reader : RulesReaders.READERS) {
            for (List<Written> system : systems()) {
                RulesReaders.theOrderTheRulesArrivedInIsNotPartOfTheAnswer(reader, system,
                        stated -> everyOrder(stated));
            }
        }
    }

    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        for (Reader reader : RulesReaders.READERS) {
            for (List<Written> system : systems()) {
                RulesReaders.sayingARuleTwiceSaysWhatSayingItOnceSays(reader, system);
            }
        }
    }

    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        assertEquals(Set.of(Rel.values()), relationsIn(OVER_THREE),
                "a relation no system is written with is one no reading of it is asked about");
        for (Reader reader : RulesReaders.READERS) {
            Tally tally = new Tally();
            for (List<Written> system : systems()) {
                RulesReaders.noPointTheRulesAdmitIsRefused(reader, system, tally);
            }
            RulesReaders.assertBothWaysWereChecked(reader, tally, 0);
        }
    }
}
