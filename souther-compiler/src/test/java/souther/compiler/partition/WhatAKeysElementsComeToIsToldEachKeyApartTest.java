package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the elements of a key come to is told of each key apart: where a row holds nothing at a
 * field of an element of one key, the elements of another key still come to their number, and
 * only the key whose element held nothing is told so. A row holding nothing at an element's key
 * is another matter — that element may be of any key, so no key's number is told.
 *
 * <p>Held where a row's reading of a key's number is made ({@link WhatATermRead#underItsKey}),
 * with a row that put each posting's fields where it did, and wrote nothing at some of them under
 * this reading.
 */
class WhatAKeysElementsComeToIsToldEachKeyApartTest {

    private static final TermPath POSTINGS = TermPath.of("ps");

    private static final ElementProjection ACCOUNT =
            ElementProjection.ofFields(List.of("account"));

    private static final ElementProjection AMOUNT = ElementProjection.ofFields(List.of("amount"));

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    private static final NumericTerm.GatheredUnderItsKey TOTAL =
            NumericTerm.GatheredUnderItsKey.of(POSTINGS.element(), new ElementKey.At(ACCOUNT),
                    new ElementValue.Affine(LinearForm.atom(AMOUNT)), Type.Prim.INT,
                    NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);

    private static final TermOrders ON = TermOrdersFixtures.computed(TOTAL, WHOLE, WHOLE,
            Map.of(ACCOUNT, Carrier.TEXT, AMOUNT, WHOLE));

    /** A posting's account and amount, either of them written nowhere where null. */
    private record Posting(String account, Long amount) { }

    @Test
    void anAmountWrittenNowhereUnderOneKeyLeavesAnotherKeysTotal() {
        List<Posting> postings = List.of(new Posting("a", 10L), new Posting("b", null),
                new Posting("a", 5L));
        assertEquals(new WhatATermRead.Number(Count.of(15)),
                WhatATermRead.underItsKey(ON, new Postings(postings, 0)));
        assertInstanceOf(WhatATermRead.NothingWrittenThere.class,
                WhatATermRead.underItsKey(ON, new Postings(postings, 1)));
    }

    @Test
    void anAccountWrittenNowhereLeavesNoKeysTotal() {
        List<Posting> postings = List.of(new Posting("a", 10L), new Posting(null, 3L));
        assertInstanceOf(WhatATermRead.NothingWrittenThere.class,
                WhatATermRead.underItsKey(ON, new Postings(postings, 0)));
    }

    /**
     * A candidate read back, one of whose elements is of another shape than the walk's, is one
     * the reading could not tell about — never one standing somewhere else: that element may be
     * of the key, and what it holds is no part of what was read.
     */
    @Test
    void aCandidateWithAnElementOfAnotherShapeIsNotSaidToStandElsewhere() {
        ObservedValue posting = new ObservedValue.Constructed(
                TypeSymbols.declared(new TypeKey("demo", "Posting")),
                Map.of("account", new ObservedValue.Text("a"),
                        "amount", new ObservedValue.Integer(10)));
        assertEquals(new Generator.RealizationReadback.CouldNotTell(
                        new Generator.ReadbackGap.WalkAndTypeDisagree()),
                Generator.readBack(ON, List.of(posting, new ObservedValue.Integer(3)),
                        Count.of(10)));
    }

    /** One list of postings, read with the posting at {@code chosen} chosen. */
    private record Postings(List<Posting> each, int chosen) implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            Posting posting = each.get(chosen);
            boolean account = path.steps().getLast().toString().equals("account");
            Object held = account ? posting.account() : posting.amount();
            if (held == null) {
                return WalkResult.reached(new ObservationAtPoint.WroteNothing());
            }
            return WalkResult.reached(new ObservationAtPoint.Value(account
                    ? new ObservedValue.Text(posting.account())
                    : new ObservedValue.Integer(posting.amount())));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            throw new UnsupportedOperationException("a key's number reads its elements one by one");
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (int at = 0; at < each.size(); at++) {
                out.add(new Postings(each, at));
            }
            return WalkResult.reached(out);
        }
    }
}
