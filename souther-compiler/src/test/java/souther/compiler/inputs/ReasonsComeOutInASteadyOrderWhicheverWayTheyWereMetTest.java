package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Clause;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a question stands on comes out the same however the walk met it.
 *
 * <p>No order of anybody's is claimed here: which of two reasons an author wrote first is settled
 * by where they wrote them, and that is asked where the places are. What is held is the other half
 * of the old claim, and it is a claim about this compiler rather than about a model — a projection
 * out of this reaches a document, so a sequence left to whichever order a walk happened to take
 * would have one compiler over one source publish two documents, and which one an author saw would
 * be the run they happened to make.
 *
 * <p>Measured by handing the same reasons over in several orders. Nothing else changes, so anything
 * that comes out different is settled by the order they arrived in and by nothing else.
 */
class ReasonsComeOutInASteadyOrderWhicheverWayTheyWereMetTest {

    /**
     * Every reason at one site, and every site beside one reason, in any order.
     *
     * <p>Read off the types ({@link ValuesOfAType}), so two reasons of one kind that differ in what
     * the kind holds are among them, and so are two sites alike in everything but one component.
     */
    @Test
    void everyReasonAtEverySiteComesOutTheSameInAnyOrder() {
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

    /** And two about two things are two entries, which is what the comparison above is over. */
    @Test
    void andTwoThingsAreTwoEntries() {
        BlockReason.RuleReadingStopped form = new BlockReason.UnreadComparisonForm();
        assertEquals(2, RuleReasons.from(List.of(said(0, form), said(1, form))).said().size(),
                "an author wrote two of them and has two things to look at, and the word says"
                        + " neither");
    }

    /** One reason about the part numbered {@code part}, sent to the rule as a whole. */
    private static RuleReasons.Said said(int part, BlockReason.RuleReadingStopped reason) {
        return new RuleReasons.Said(RuleSite.at(new PartId<>(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("demo", "N")), 0),
                Optional.empty())), part)), RuleSite.theRuleItself(), reason);
    }
}
