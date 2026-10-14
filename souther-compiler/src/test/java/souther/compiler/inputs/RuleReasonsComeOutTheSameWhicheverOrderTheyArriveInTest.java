package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Reasons put together come out as one value whichever order a walk met them in.
 *
 * <p>What {@link RuleReasons#from} is for. What it returns is held inside answers and written into a
 * document, so a sequence that followed the walk would make one compiler over one source answer
 * two ways. The orders it sorts by are each asked on their own
 * ({@code ASteadyOrderTellsApartWhateverEqualityTellsApartTest}); this asks the one thing they are
 * put together for.
 *
 * <p>Over values read off the type, so every reason is among them at one site, and every site
 * beside one reason: two reasons of one kind that differ in what the kind holds are two of them.
 */
class RuleReasonsComeOutTheSameWhicheverOrderTheyArriveInTest {

    @Test
    void everyReasonAtEverySiteInAnyOrder() {
        List<RuleReasons.Said> said = new ArrayList<>();
        new ValuesOfAType().of(RuleReasons.Said.class)
                .forEach(each -> said.add((RuleReasons.Said) each));
        RuleReasons forwards = RuleReasons.from(said);
        List<RuleReasons.Said> backwards = new ArrayList<>(said);
        Collections.reverse(backwards);
        assertEquals(forwards, RuleReasons.from(backwards));
        List<RuleReasons.Said> turned = new ArrayList<>(said);
        Collections.rotate(turned, said.size() / 2);
        assertEquals(forwards, RuleReasons.from(turned));
    }
}
