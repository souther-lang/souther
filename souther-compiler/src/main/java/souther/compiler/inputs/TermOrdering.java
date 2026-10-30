package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.NumericAnswers;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Both orders a term stands on, worked out from what stands where its number comes from.
 *
 * <p>The one place the derivation lives, and not reachable from a term. A term is a value that
 * travels, and a type is in every reader's hand, so a derivation written on the term is a question
 * anything holding the two can answer — about wherever that type came from, and about no reading in
 * particular. What settles where a term's number comes from is the reading of the input, so the one
 * caller here is {@link ReadQuantities#ordersOf}, which puts the reading's own answer in.
 *
 * <p>What the answer is about is therefore the reading's to say, and every other layer asks
 * {@link Quantities#ordersOf} for it rather than working it out again.
 */
final class TermOrdering {

    private TermOrdering() { }

    /**
     * Both ends together, which is what every reader of a row wants and what neither end alone is
     * safe to stand in for. A term that is what a location holds has one order twice, and says so
     * here rather than by two readings that happen to agree.
     */
    static TermOrders of(NumericTerm term, Type positionType, Symbols symbols,
                         DeclarationAccess declarations) {
        return of(term, positionType, Map.of(), Map.of(), symbols, declarations);
    }

    /**
     * The same, for a term read off the places of an element: one over what a walk computed of
     * each element, whose value is read on the type the computation stands as and whose fields are
     * read on their own, and one read among an element's neighbours.
     *
     * @param fieldTypes what stands at each field whose number is read
     * @param onTheWay   what stands at each place on the way to every place read of an element,
     *                   the element itself among them, which says the names a value there is
     *                   written inside
     */
    static TermOrders of(NumericTerm term, Type positionType,
                         Map<ElementProjection, Type> fieldTypes,
                         Map<ElementProjection, Type> onTheWay, Symbols symbols,
                         DeclarationAccess declarations) {
        Carrier observed = observedOn(positionType, declarations);
        // One construction and not one per arm. A term that is a location's own content answers on
        // the order its value is read on, which is that order twice rather than a second way of
        // making a pair — and a second way is a second place a pair can come from.
        Carrier answered = switch (term) {
            // The end of a key's values is one of the values, so it is measured where they are;
            // and what a key's numbers come to is measured on what each of them stands as.
            case NumericTerm.ValueOf _, NumericTerm.GatheredUnderItsKey _,
                 NumericTerm.GatheredUnderAKey _ -> observed;
            // Unless it is the end of the steps the values fall in, which are counted on the order
            // of the steps and not of the values.
            case NumericTerm.ExtremeOfItsKey extreme -> extreme.through() == null ? observed
                    : answeredOn(term, positionType, symbols, declarations);
            case NumericTerm.TakenOf _, NumericTerm.CodePointClassCount _,
                 NumericTerm.CodePointValueSum _, NumericTerm.CodePointAt _,
                 NumericTerm.WholeUnitsOf _, NumericTerm.Multiplicity _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.TakenOver _ -> answeredOn(term, positionType, symbols, declarations);
            case NumericTerm.ProductOf _ -> throw new IllegalArgumentException(
                    term + " is made of the orders of its factors (ofAProduct)");
        };
        Map<ElementProjection, Carrier> fields = new LinkedHashMap<>();
        fieldTypes.forEach((field, type) -> {
            Carrier on = observedOn(type, declarations);
            if (on != null) {
                fields.put(field, on);
            }
        });
        Map<ElementProjection, List<TypeSymbol>> worn = new LinkedHashMap<>();
        for (Map.Entry<ElementProjection, Type> each : onTheWay.entrySet()) {
            List<TypeSymbol> names = namesWorn(each.getValue(), declarations.inners());
            if (!names.isEmpty()) {
                worn.put(each.getKey(), names);
            }
        }
        return new TermOrders(term, observed, answered, fields, worn);
    }

    /** What a reading answers of one number: the orders it stands on, or null. */
    interface OfTheNumbers {
        TermOrders of(NumericTerm number);
    }

    /**
     * The orders of a product of two forms, which is counted on decimals where any of its numbers
     * is and on whole numbers where all are, and on no order where one is counted on another: a
     * product of a date and a count is the product of nothing.
     *
     * @param reading the orders of a number either form is of
     */
    static TermOrders ofAProduct(NumericTerm.ProductOf term, OfTheNumbers reading) {
        Carrier on = null;
        List<TermOrders> factors = new ArrayList<>();
        for (LinearForm<NumericTerm> form : term.factors()) {
            for (NumericTerm number : form.coefs().keySet()) {
                TermOrders each = reading.of(number);
                if (each == null || !(each.answered() instanceof Carrier.Whole
                        || each.answered() instanceof Carrier.Dense)) {
                    return new TermOrders(term, null, null);
                }
                // A whole number beside a decimal is multiplied as decimals are.
                if (on == null || each.answered() instanceof Carrier.Dense) {
                    on = each.answered();
                }
                factors.add(each);
            }
        }
        return on == null ? new TermOrders(term, null, null)
                : new TermOrders(term, on, on, Map.of(), Map.of(), factors);
    }

    /**
     * Every name a value of {@code type} is written inside, outermost first: what a reader of an
     * observed element takes off, by name, before each step it takes into it.
     */
    private static List<TypeSymbol> namesWorn(Type type, NewtypeInners inners) {
        return TypeOps.newtypeSpine(type, inners).layers().stream()
                .map(TypeOps.Layer::named).toList();
    }

    /**
     * The order the number a term names is measured on, or null where it has none.
     *
     * <p>What a rule about the length of a string is counted as is an {@code Int} at a position no
     * line is drawn on, and what a rule about {@code Time.hour(t)} is counted as is a count by one at
     * a position counting the seconds of its day. Both follow from what the operation answers and
     * from nothing about where it was applied — asked of the position, the step of the answer was
     * the step of the argument, and the twelfth hour was a line at the twelfth second.
     *
     * <p>Which is why {@code positionType} may be absent. A term under more steps than the walk that
     * finds an input's positions goes down has no position to ask, and what an operation answers is
     * what it answers all the same. What is null there is a term measured by its own values, which
     * is the one case the position was the answer to.
     */
    private static Carrier answeredOn(NumericTerm term, Type positionType, Symbols symbols,
                                      DeclarationAccess declarations) {
        NewtypeInners inners = declarations.inners();
        return switch (term) {
            case NumericTerm.ValueOf _, NumericTerm.GatheredUnderItsKey _,
                 NumericTerm.GatheredUnderAKey _ ->
                    positionType == null ? null
                    : Carrier.ofValue(positionType, declarations);
            case NumericTerm.ExtremeOfItsKey extreme -> extreme.through() != null
                    ? Carrier.ofValue(DefaultBoundOperationFacts.get()
                            .wholeUnitsAnswered(extreme.through()), declarations)
                    : positionType == null ? null : Carrier.ofValue(positionType, declarations);
            case NumericTerm.TakenOf taken -> {
                Type answers =
                        NumericAnswers.typeOf(taken.operation(), positionType, inners, symbols);
                yield answers == null ? null : Carrier.ofValue(answers, declarations);
            }
            // How many code points there are is a whole number whatever they are code points of,
            // as how many a container holds is.
            case NumericTerm.CodePointClassCount _ -> Carrier.ofValue(Type.Prim.INT, declarations);
            // What the code points come to is the whole number the list of them adds up to.
            case NumericTerm.CodePointValueSum _ -> Carrier.ofValue(Type.Prim.INT, declarations);
            // A code point is the whole number `String.codePoints` lists it as.
            case NumericTerm.CodePointAt _ -> Carrier.ofValue(Type.Prim.INT, declarations);
            // The step of the order the operation answers on, which is not the order of the value
            // it is the step of: a date counts days where the date-time it falls on counts seconds.
            case NumericTerm.WholeUnitsOf units -> Carrier.ofValue(
                    DefaultBoundOperationFacts.get().wholeUnitsAnswered(units.operation()),
                    declarations);
            // How often a value occurs is a whole number whatever the value is.
            case NumericTerm.Multiplicity _, NumericTerm.OccurrencesOfItsValue _,
                 NumericTerm.OccurrencesOfAKey _ -> Carrier.ofValue(Type.Prim.INT, declarations);
            // Asked of the operation as a taking is, and asked of what it was given: a run is a
            // container of the values standing at the place it is read from, so what the operation
            // answers of one is what it answers of a container of them. Written out here as the
            // element's own order instead, this would be the account of a walk that adds restated
            // for every account, and the first one that answers something else would be read as
            // answering what its elements are.
            case NumericTerm.TakenOver over -> {
                Type answers = positionType == null ? null : NumericAnswers.typeOf(
                        over.operation(), new Type.ListOf(positionType), inners, symbols);
                yield answers == null ? null : Carrier.ofValue(answers, declarations);
            }
            // Counted on the order its factors are ({@link #ofAProduct}), not on a type.
            case NumericTerm.ProductOf _ -> null;
        };
    }

    /**
     * The order a value at the term's path is decoded on, or null where nothing orders it.
     *
     * <p>The other end of the same term, and null for more than one reason. A container is not
     * ordered and is read by what it holds rather than by a count of its own; a position whose type
     * nothing here can follow has no order either. Both are answers a reader can act on — what is
     * refused is silently reading the value on the order its answer is measured on, which is right
     * for every operation whose two ends agree and wrong without a word for the first that does not.
     */
    private static Carrier observedOn(Type positionType, DeclarationAccess declarations) {
        return positionType == null ? null : Carrier.ofValue(positionType, declarations);
    }
}
