package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a container states of every element it holds, put as clauses of the value one element is.
 *
 * <p>A statement is written about the element its predicate names, and read of the value standing
 * here, which is that element: so it is carried over by putting this value where the predicate
 * names its parameter. That is the whole of the translation, and what cannot be put that way is not
 * read — never read as something else. A statement is carried over only where
 *
 * <ul>
 *   <li>the value it names is this one, and its only way to say so is one of this value's places:
 *       a value that is its own value, which a newtype and what no declaration stands under are,
 *       stands as the type it was written as; a record is read through its fields, so
 *       {@code e.size} is the field {@code size};
 *   <li>it reads no name but the element and the ones it makes itself. What else it names is the
 *       container's, which a reading of one element has no place for; and the fields of a
 *       declaration are the same bindings wherever the declaration is, so one read here would be
 *       taken for this value's own;
 *   <li>the rule it is a part of is not one this value is read under already. A reading answers
 *       once for a rule, and the same rule as the declaration's own and as what its container
 *       states of an element of that declaration are two statements it cannot keep apart.
 * </ul>
 *
 * <p>A statement left out is said so, and the position is read as short of it.
 */
final class ElementStatements {

    private ElementStatements() {}

    /** What a value that is its own value is read by, where no declaration names it. */
    static final String THE_VALUE = "value";

    /**
     * Where the statements are read.
     *
     * @param atTheValue whether the value is its own value, and not a record of fields
     * @param element    what the element is, which is what its container wrote its statements about
     * @param fields     what each name of the value is a place of, and of what type
     * @param bindings   the binding each name of the value stands for
     */
    record Frame(boolean atTheValue, Type element, Map<String, Type> fields,
                 Map<String, BindingId> bindings) {}

    /**
     * What was carried over: one clause for each rule of the container, with the parts that state
     * something of the value joined as its author joined them and each under its own name.
     *
     * @param clauses     the clause of each rule, in the order the rules were met
     * @param someLeftOut whether a statement was left out
     */
    record CarriedOver(Map<RuleRef.Invariant, Clauses.AsStated> clauses, boolean someLeftOut) {}

    /** The statements of {@code guarantees} as clauses of the value {@code frame} says. */
    static CarriedOver carry(List<ElementGuarantee> guarantees, Frame frame,
                             Set<RuleRef.Invariant> readAsItsOwn) {
        // What a part states first, as the part: one part an author wrote can state several things
        // of every element — a helper it calls states two — and it is still the one part, which a
        // reading is made without as a whole and whose place in a statement is one.
        Map<PartId<RuleRef.Invariant>, OfAPart> ofAPart = new LinkedHashMap<>();
        boolean someLeftOut = false;
        for (ElementGuarantee each : guarantees) {
            Core stated = readAsItsOwn.contains(each.part().rule()) ? null : ofTheValue(each, frame);
            if (stated == null) {
                someLeftOut = true;
                continue;
            }
            ofAPart.merge(each.part(), new OfAPart(stated, statementsOf(each, stated)),
                    OfAPart::and);
        }
        // And then the rule, whose parts are joined as its author joined them.
        Map<RuleRef.Invariant, Clauses.AsStated> clauses = new LinkedHashMap<>();
        ofAPart.forEach((part, stated) -> clauses.merge(part.rule(),
                new Clauses.AsStated(stated.states(), new ClauseMeaning.Parts.One(part, Set.of(),
                        stated.statements())),
                ElementStatements::joined));
        return new CarriedOver(clauses, someLeftOut);
    }

    /** What one part states of the value, and the identity of each statement it comes to. */
    private record OfAPart(Core states, List<StatementNumber> statements) {

        OfAPart and(OfAPart other) {
            List<StatementNumber> both = new ArrayList<>(statements);
            both.addAll(other.statements);
            return new OfAPart(both(states, other.states), both);
        }
    }

    /**
     * The number of each statement {@code stated} comes to, which the statement of the container
     * that says it issues, once. Counted by the shape's walk, as the reading that reads it will
     * count them, so that the two agree about how many there are.
     */
    private static List<StatementNumber> statementsOf(ElementGuarantee guarantee, Core stated) {
        int count = ConjunctStatements.statedBy(ClauseExpr.of(stated, true)).size();
        List<StatementNumber> out = new ArrayList<>();
        for (int each = 0; each < count; each++) {
            out.add(guarantee.statedBy().number().stating(each));
        }
        return out;
    }

    /** What {@code guarantee} states with the value put where its predicate names the element, or
     *  null where that is not something this value has a place for. */
    private static Core ofTheValue(ElementGuarantee guarantee, Frame frame) {
        BindingId parameter = guarantee.predicate().params().getFirst().binding();
        Core body = guarantee.predicate().body();
        // The element and what the statement makes itself are the only names it may read. Any other
        // is the container's — a field of the value that holds the list, or of its declaration —
        // and has no place in a reading of one element: one of this value's own bindings would be
        // taken for the element's, and any other would be a value nothing here says anything of.
        Set<BindingId> free = WhatABodyReads.freeIn(body);
        free.remove(parameter);
        if (!free.isEmpty()) {
            return null;
        }
        if (frame.atTheValue()) {
            BindingId value = frame.bindings().get(THE_VALUE);
            // Standing where the statement was written, which is where the element is named.
            return value == null ? null : Clauses.substituted(body, Map.of(parameter,
                    new Core.Read(THE_VALUE, value, frame.element(), guarantee.predicate().pos())));
        }
        Core ofItsFields = withItsFieldsRead(body, parameter, frame);
        return WhatABodyReads.binding(ofItsFields, parameter) ? null : ofItsFields;
    }

    /** {@code e} with each field of {@code element} that it reads read as the field itself. */
    private static Core withItsFieldsRead(Core e, BindingId element, Frame frame) {
        if (Core.withoutStanding(e) instanceof Core.FieldAccess access
                && Core.withoutStanding(access.target()) instanceof Core.Read target
                && target.binding().equals(element)
                && frame.bindings().containsKey(access.field())) {
            return new Core.Read(access.field(), frame.bindings().get(access.field()),
                    frame.fields().get(access.field()), access.pos());
        }
        return Core.mapAll(e, child -> withItsFieldsRead(child, element, frame), name -> name);
    }

    /** Two statements that both hold. */
    private static Core both(Core left, Core right) {
        return new Core.Binary(ConditionJoin.BOTH.operator(), left, right,
                Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(), Type.BOOL,
                left.pos());
    }

    /** Two clauses stated together, as one clause of two parts. */
    private static Clauses.AsStated joined(Clauses.AsStated left, Clauses.AsStated right) {
        return new Clauses.AsStated(both(left.states(), right.states()),
                new ClauseMeaning.Parts.Both(left.parts(), right.parts()));
    }
}
