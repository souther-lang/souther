package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A form coming out a way is asked of the region of a reading once, and what comes back is what
 * the region itself says of that form and that way.
 */
class AFormTakenInOverOneReadingIsAskedOfItsRegionOnceTest {

    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int) -> Ok
            """;

    private static final InputReading READING = reading();

    @Test
    void theSameFormAndWayAreAnsweredOnceAndTheAnswerIsTheRegionsOwn() {
        FormsTakenIn forms = FormsTakenIn.of(READING);
        SearchRegion.Assumption first = forms.assuming(form(-1, 1, 0), Rel.LE);
        assertSame(first, forms.assuming(form(-1, 1, 0), Rel.LE));
        assertSame(forms, FormsTakenIn.of(READING));
        assertEquals(READING.quantities().region().assuming(form(-1, 1, 0), Rel.LE).taken()
                        .projectionOf(term("x")),
                first.taken().projectionOf(term("x")));
    }

    @Test
    void aDifferentWayOrAFormIsAskedAgain() {
        FormsTakenIn forms = FormsTakenIn.of(READING);
        SearchRegion.Assumption below = forms.assuming(form(-1, 1, 0), Rel.LE);
        SearchRegion.Assumption above = forms.assuming(form(-1, 1, 0), Rel.GE);
        SearchRegion.Assumption other = forms.assuming(form(-1, 1, 5), Rel.LE);
        assertNotSame(below, above);
        assertNotSame(below, other);
        for (Rel rel : List.of(Rel.LE, Rel.GE)) {
            for (long constant : List.of(0L, 5L)) {
                assertEquals(
                        READING.quantities().region().assuming(form(-1, 1, constant), rel).taken()
                                .projectionOf(term("x")),
                        forms.assuming(form(-1, 1, constant), rel).taken()
                                .projectionOf(term("x")),
                        rel + " " + constant);
            }
        }
    }

    private static LinearForm<NumericTerm> form(long cx, long cy, long k) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(term("x"), ExactRatio.of(cx));
        coefs.put(term("y"), ExactRatio.of(cy));
        return new LinearForm<>(ExactRatio.of(k), coefs);
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        TermPath path = READING.domain().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError("no position at " + spelled));
        return new NumericTerm.ValueOf(path);
    }

    private static InputReading reading() {
        Compilation compilation =
                Compilation.ofSources(List.of(PAIR), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("read"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none()).reading(rules);
    }
}
