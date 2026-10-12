package souther.compiler.query;

import souther.compiler.partition.Axis;
import souther.compiler.partition.ClassCoexistence;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.PartitionClass;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count of a container that admits nothing in it and a class of a position inside the container
 * are no combination, in the count and in what is owed.
 *
 * <p>An empty list has no element to hold a field, so no row sits in both — that is the model
 * saying so, the way a position under one case of a sum is in no value of another case
 * ({@link ACombinationTheModelCannotHoldIsNoRequirementTest}). Owed there, the combination is a gap a
 * strict build refuses over and nothing can close.
 *
 * <p>Only where every count the class holds is below one. A class holding a count of one holds a
 * list with an element, and a class of a count of something made from the list, or of a container
 * the position is not inside, says nothing about whether the position is there.
 */
class AnEmptyContainerPairsWithNothingInsideItTest {

    private static final String QUOTE = """
            module example.quote

            import List ( filter, all, length )

            data Item = { quantity: Int, unitPrice: Int }
            data Cart = { items: List<Item> }

            data Empty
            data Bad = { count: Int }
            data Priced = { total: Int }

            behavior quote : (c: Cart) -> Priced | Empty | Bad
                constructs Priced, Bad

            let quote (c) = {
                guard length(c.items) >= 1 else Empty
                guard all(i -> i.quantity >= 1, c.items) else Bad { count = length(filter(i -> i.quantity < 1, c.items)) }
                Priced { total = 0 }
            }

            example quote
                | "empty" : (Cart { items = [] }) -> Empty
                | "bad" : (Cart { items = [Item { quantity = 0, unitPrice = 1 }] }) -> Bad { count = 1 }
                | "ok" : (Cart { items = [Item { quantity = 1, unitPrice = 1 }] }) -> Priced { total = 0 }
            """;

    /**
     * The empty list's class makes no combination with the element's classes, and the non-empty
     * one makes both — so the rows written reach every combination there is.
     */
    @Test
    void anEmptyListPairsWithNoClassOfItsElements() {
        Measured quote = quote();

        assertEquals(2, quote.sizeOf("List.length(c.items)", "c.items[*].quantity"),
                () -> "the list with an element meets both classes of what it holds, and the empty"
                        + " list neither: " + quote.dump());
        assertEquals(List.of(), quote.owed(), quote::dump);
        assertEquals(List.of(), quote.pairGaps(),
                () -> "a strict build has nothing to refuse over: " + quote.dump());
    }

    /**
     * Whichever of the two positions is named first.
     *
     * <p>Asked directly, because the walk happens to put the count before what the list holds, and
     * a pair space alone never asks the other way round.
     */
    @Test
    void theAnswerDoesNotTurnOnWhichPositionIsNamedFirst() {
        Measured quote = quote();
        Axis length = quote.axis("List.length(c.items)");
        Axis quantity = quote.axis("c.items[*].quantity");

        ClassCoexistence countFirst = ClassCoexistence.between(length, quantity);
        ClassCoexistence countSecond = ClassCoexistence.between(quantity, length);
        for (int count = 0; count < length.classes().size(); count++) {
            for (int held = 0; held < quantity.classes().size(); held++) {
                String named = length.classes().get(count).id() + " with "
                        + quantity.classes().get(held).id();
                boolean empty = length.classes().get(count).id()
                        .equals("List.length(c.items)/0 <= x <= 0");
                assertEquals(!empty, countFirst.canHoldTogether(count, held), named);
                assertEquals(!empty, countSecond.canHoldTogether(held, count), named);
            }
        }
    }

    /** A class holding a count of one holds a list with an element, so it is kept whole. */
    @Test
    void aClassThatHoldsACountOfOneIsKept() {
        Measured few = measured("""
                module example.few

                import List ( all, length )

                data Item = { quantity: Int }
                data Cart = { items: List<Item> }
                data Out = Int

                behavior few : (c: Cart) -> Out
                    constructs Out

                let few (c) = {
                    guard length(c.items) <= 1 else Out(0)
                    guard all(i -> i.quantity >= 1, c.items) else Out(1)
                    Out(2)
                }

                example few
                    | (Cart { items = [Item { quantity = 1 }] }) -> Out(2)
                """, "example.few", "few");

        assertEquals(4, few.sizeOf("List.length(c.items)", "c.items[*].quantity"),
                () -> "each class of the length holds a list with an element: " + few.dump());
    }

    /** A position the list does not hold is there whether or not the list holds anything. */
    @Test
    void aPositionOutsideTheListIsKept() {
        Measured noted = measured("""
                module example.noted

                import List ( length )

                data Item = { quantity: Int }
                data Cart = { items: List<Item>, note: Int }
                data Out = Int

                behavior noted : (c: Cart) -> Out
                    constructs Out

                let noted (c) = {
                    guard length(c.items) >= 1 else Out(0)
                    guard c.note >= 1 else Out(1)
                    Out(2)
                }

                example noted
                    | (Cart { items = [Item { quantity = 1 }], note = 1 }) -> Out(2)
                """, "example.noted", "noted");

        assertEquals(4, noted.sizeOf("List.length(c.items)", "c.note"),
                () -> "an empty list and a note of either class are one value: " + noted.dump());
    }

    /**
     * Every container a position is inside has to hold something for it to be there, so an empty
     * outer list pairs with nothing under it — the inner list's count included — and an empty inner
     * list with nothing under that one.
     */
    @Test
    void eachContainerAPositionIsInsideHasToHoldSomething() {
        Measured nested = measured("""
                module example.nested

                import List ( all, length )

                data Part = { q: Int }
                data Line = { parts: List<Part> }
                data Order = { lines: List<Line> }
                data Out = Int

                behavior nested : (o: Order) -> Out
                    constructs Out

                let nested (o) = {
                    guard length(o.lines) >= 1 else Out(0)
                    guard all(l -> length(l.parts) >= 1, o.lines) else Out(1)
                    guard all(l -> all(p -> p.q >= 1, l.parts), o.lines) else Out(2)
                    Out(3)
                }

                example nested
                    | (Order { lines = [Line { parts = [Part { q = 1 }] }] }) -> Out(3)
                """, "example.nested", "nested");

        assertEquals(2, nested.sizeOf("List.length(o.lines)", "o.lines[*].parts[*].q"),
                () -> "an empty outer list holds no part: " + nested.dump());
        assertEquals(2, nested.sizeOf("List.length(o.lines[*].parts)", "o.lines[*].parts[*].q"),
                () -> "an empty inner list holds no part: " + nested.dump());
        assertEquals(2, nested.sizeOf("List.length(o.lines)", "List.length(o.lines[*].parts)"),
                () -> "an empty outer list holds no inner list to count: " + nested.dump());
    }

    /** A map holds its values the way a list holds its elements. */
    @Test
    void anEmptyMapPairsWithNoClassOfItsValues() {
        Measured usage = measured("""
                module example.usage

                data Usage = { counts: Map<String, Int> }
                data Out = Int

                behavior northern : (u: Usage) -> Out
                    constructs Out

                let northern (u) = {
                    guard Map.size(u.counts) >= 1 else Out(0)
                    guard Map.fold((acc, _, v) -> acc && v >= 1, true, u.counts) else Out(1)
                    Out(2)
                }

                example northern
                    | (Usage { counts = [("north", 5)] }) -> Out(2)
                """, "example.usage", "northern");

        assertEquals(2, usage.sizeOf("Map.size(u.counts)", "u.counts[*]"),
                () -> "an empty map holds no value of either class: " + usage.dump());
    }

    private record Measured(String behavior, Compilation compilation, PartitionEvidence evidence,
                            MeasuredInput subject) {

        /** How many combinations the space holds between the two numbers. */
        long sizeOf(String one, String other) {
            for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
                String a = pair.between().one().term();
                String b = pair.between().other().term();
                if ((a.equals(one) && b.equals(other)) || (a.equals(other) && b.equals(one))) {
                    return pair.total();
                }
            }
            throw new AssertionError("no relation between " + one + " and " + other + ": " + dump());
        }

        Axis axis(String term) {
            return subject.axes().axes().stream().filter(each -> each.id().term().equals(term))
                    .findFirst().orElseThrow(() -> new AssertionError("no axis " + term + dump()));
        }

        List<ObligationIdentity.OfAFallbackPairCell> owed() {
            return Coverages.uncovered(behavior, subject.axes(), evidence.pairs());
        }

        List<String> pairGaps() {
            return AdequacyReport.of(compilation).adequacyGaps().stream()
                    .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                    .map(each -> each.about().toString())
                    .toList();
        }

        String dump() {
            StringBuilder out = new StringBuilder();
            for (Axis axis : subject.axes().axes()) {
                out.append("\n  ").append(axis.id()).append(':');
                for (PartitionClass each : axis.classes()) {
                    out.append(" [").append(each.id()).append(']');
                }
            }
            out.append("\n  space: ").append(evidence.pairs().space());
            return out.toString();
        }
    }

    /** One compilation of {@link #QUOTE} for every question here asked of it. */
    private static Measured quote() {
        if (QUOTE_ANSWERED == null) {
            QUOTE_ANSWERED = measured(QUOTE, "example.quote", "quote");
        }
        return QUOTE_ANSWERED;
    }

    private static Measured QUOTE_ANSWERED;

    private static Measured measured(String model, String module, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage(module)).value();
        PartitionEvidence said = coverage == null ? null : coverage.get(behavior);
        MeasuredInput subject = Adequacy.subjectOf(compilation.db(), module, behavior);
        assertTrue(said != null && subject != null, () -> behavior + " was not measured: "
                + compilation.diagnostics());
        return new Measured(behavior, compilation, said, subject);
    }
}
