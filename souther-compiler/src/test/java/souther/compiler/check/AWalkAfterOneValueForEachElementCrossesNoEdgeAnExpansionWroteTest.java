package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.carrier.Membership;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.OnePerElement;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.ValueDefinitions;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A walk after which container a list holds one value for each element of, or holds something
 * exactly where, crosses no edge an expansion wrote, and reads what a binding holds where none was
 * written.
 *
 * <p>An edge saying a binding holds the same values as another does not say as often — what kept
 * some of the elements has that edge — and one saying its values were made from another's says
 * nothing of how many were made of each. Neither is a run of one for each element, and neither is
 * a list holding something where the other does. Where nothing was written, what the binding holds
 * is all there is, and it is read.
 *
 * <p>Written out rather than compiled, because the walk is asked of a name the reading cannot
 * resolve by itself, which is the case the step through a name exists for.
 */
class AWalkAfterOneValueForEachElementCrossesNoEdgeAnExpansionWroteTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("example.walks", "f");

    /** The parameter the container's binding was bound to. */
    private static final BindingId HELD = new BindingId(OWNER, 0);

    /** The parameter an edge runs to. */
    private static final BindingId OTHER = new BindingId(OWNER, 1);

    /** The list the walk is asked of, bound to the first parameter. */
    private static final BindingId CONTAINER = new BindingId(OWNER, 2);

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final DeclarationNewtypes NEWTYPES = DeclarationNewtypes.asWritten(SYMBOLS);

    private static Core.Read read(String name, BindingId binding) {
        return new Core.Read(name, binding, Type.list(Type.INT), POS);
    }

    private static InputReads reads(ElementProvenance provenance) {
        ElementBindings elements = new ElementBindings(Map.of(),
                Map.of(CONTAINER, read("held", HELD)), provenance, Map.of());
        return InputReads.ofParameters(Map.of(HELD, "held", OTHER, "other"),
                DeclaredInput.NONE, elements, ValueDefinitions.NONE, Membership.none());
    }

    private static ElementProvenance theSameAs() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        builder.holdsTheSameAs(CONTAINER, OTHER);
        return builder.built();
    }

    private static ElementProvenance madeFrom() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        builder.derivesFrom(CONTAINER, OTHER);
        return builder.built();
    }

    private static OnePerElement onePerElement(ElementProvenance provenance) {
        return reads(provenance).onePerElementOf(read("xs", CONTAINER), SYMBOLS, NEWTYPES);
    }

    private static PathResolution holdingSomething(ElementProvenance provenance) {
        return reads(provenance).holdingSomethingWhere(read("xs", CONTAINER), SYMBOLS, NEWTYPES);
    }

    @Test
    void whereNothingWasWrittenWhatTheBindingHoldsIsRead() {
        assertEquals(new OnePerElement(TermPath.of("held"), new ElementProjection(List.of()),
                false), onePerElement(ElementProvenance.NONE));
        assertEquals(new PathResolution.At(TermPath.of("held")),
                holdingSomething(ElementProvenance.NONE));
    }

    /**
     * A list standing as a wider type holds values what the wider type calls equal, which is not
     * shown to be what the narrower one does: it is no run of one value for each element even where
     * it names a position, and still holds something exactly where that position does.
     */
    @Test
    void aListStandingWiderIsNoRunOfOneValueEachAndStillHoldsSomethingWhereItsContainerDoes() {
        Core wider = new Core.Widen(read("held", HELD), Type.list(Type.DECIMAL));
        InputReads reads = reads(ElementProvenance.NONE);
        assertNull(reads.onePerElementOf(wider, SYMBOLS, NEWTYPES));
        assertEquals(new PathResolution.At(TermPath.of("held")),
                reads.holdingSomethingWhere(wider, SYMBOLS, NEWTYPES));
        assertEquals(new OnePerElement(TermPath.of("held"), new ElementProjection(List.of()),
                false), reads.onePerElementOf(read("held", HELD), SYMBOLS, NEWTYPES));
    }

    /**
     * The same where the list a name holds stands wider, which following the name sets aside: the
     * list asked of is of another type than the one reached, and that is no run of one value each.
     */
    @Test
    void aListANameHoldsStandingWiderIsNoRunOfOneValueEach() {
        ElementBindings elements = new ElementBindings(Map.of(), Map.of(CONTAINER,
                new Core.Widen(read("held", HELD), Type.list(Type.DECIMAL))),
                ElementProvenance.NONE, Map.of());
        InputReads reads = InputReads.ofParameters(Map.of(HELD, "held", OTHER, "other"),
                DeclaredInput.NONE, elements, ValueDefinitions.NONE, Membership.none());
        Core xs = new Core.Read("xs", CONTAINER, Type.list(Type.DECIMAL), POS);
        assertNull(reads.onePerElementOf(xs, SYMBOLS, NEWTYPES));
        assertEquals(new PathResolution.At(TermPath.of("held")),
                reads.holdingSomethingWhere(xs, SYMBOLS, NEWTYPES));
    }

    @Test
    void anEdgeToTheSameValuesIsNotCrossed() {
        assertNull(onePerElement(theSameAs()));
        assertEquals(new PathResolution.NotAPosition(), holdingSomething(theSameAs()));
    }

    @Test
    void anEdgeToWhatTheValuesWereMadeFromIsNotCrossed() {
        assertNull(onePerElement(madeFrom()));
        assertEquals(new PathResolution.NotAPosition(), holdingSomething(madeFrom()));
    }
}
