package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A way past a condition of several ways, where the way already asks a case that every alternative
 * but one contradicts, is looked along that one.
 *
 * <p>An alternative asking the value to be a case the way already asks it not to be is a way no row
 * takes, and is dropped; the one left is still narrower than the way whole, since it is the way
 * with that alternative taken in. So the way is split into one, which is a split and not a way with
 * nothing on it to split at.
 */
class AWayWithOneAlternativeLeftOpenIsLookedAlongThatOneTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("f", 0));

    private static final TermPath KIND = TermPath.of("k");

    @Test
    void theOneAlternativeLeftIsTheWayLookedAlong() {
        WayToTheBorder way = new WayToTheBorder(List.of(
                new OnTheWay.Narrowed(WHERE, KIND.refine(only("A")), List.of(), List.of()),
                new OnTheWay.OneOf(new ConditionOccurrence("f", 1), WHERE, List.of(
                        List.of(new OnTheWay.Narrowed(WHERE, KIND.refine(only("A")), List.of(),
                                List.of())),
                        List.of(new OnTheWay.Narrowed(WHERE, KIND.refine(only("B")), List.of(),
                                List.of()))))));
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(way, reading().quantities().region()));
        Reachability.Ways.Each each = assertInstanceOf(Reachability.Ways.Each.class,
                reaching.ways(), "split, into the one alternative some row may take");
        assertEquals(1, each.along().size(), () -> "only the alternative the way allows: " + each);
    }

    private static CasesLeft only(String name) {
        TypeSymbol leaf = TypeSymbols.declared(new TypeKey("m", name));
        return CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf), List.of(leaf)));
    }

    private static InputReading reading() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data A
                data B
                data Kind = A | B
                data Yes

                behavior f : (k: Kind) -> Yes
                let f (k) = Yes
                """, "Main");
        compilation.answerEverything();
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
