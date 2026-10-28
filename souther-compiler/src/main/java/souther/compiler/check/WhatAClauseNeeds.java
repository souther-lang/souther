package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Whether a clause cannot be true unless one part of it comes out a particular way: a lookup in a
 * map, set or list finds a member, or a call says the elements of a container are apart.
 *
 * <p>Asked by putting the part's answer in as the way it fails — a lookup finding no member (a
 * membership test false, {@code Map.get} nothing), a call saying the elements are not apart
 * (false) — and following what the clause comes to along the forms that carry an answer on: a
 * conjunction false for a false part, a disjunction false for two, a name bound to what was worked
 * out, and a match on an absent option taking its absent arm. Where the clause comes to false the
 * part is needed. Where it comes to anything else, or the part is reached some way not followed
 * here, nothing is said: a clause written as the lookup being absent, as a comparison of what it
 * found, as the elements not being apart, or as that or something else, is not shown to need it.
 *
 * <p>What a clause reads and what it needs are two things. A clause that reads a call may deny it,
 * or may hold with it false, and a reader that took the read for the need would find a rule where
 * the clause states its opposite.
 */
final class WhatAClauseNeeds {

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");

    /** The membership tests, which answer false where what is looked for is not there. */
    private static final Set<ValueName> MEMBERSHIPS = Set.of(
            ValueName.Stdlib.operation("Map", "containsKey"),
            ValueName.Stdlib.operation("Set", "contains"),
            ValueName.Stdlib.operation("List", "contains"));

    private enum Worked { FALSE, ABSENT, UNKNOWN }

    private final Core part;
    /** What the part comes to where it comes out the way it fails. */
    private final Worked failing;
    private final Map<BindingId, Worked> bound = new HashMap<>();

    private WhatAClauseNeeds(Core part, Worked failing) {
        this.part = Core.withoutStanding(part);
        this.failing = failing;
    }

    /** Whether {@code clause} is false wherever {@code lookup}, a part of it, finds no member. */
    static boolean aMemberFound(Core clause, Core lookup) {
        return new WhatAClauseNeeds(lookup, answerOfNoMember(lookup)).work(clause) == Worked.FALSE;
    }

    /** Whether {@code clause} is false wherever {@code apart}, a call of it saying the elements
     *  of a container are apart, says they are not. */
    static boolean elementsApart(Core clause, Core apart) {
        return new WhatAClauseNeeds(apart, Worked.FALSE).work(clause) == Worked.FALSE;
    }

    private Worked work(Core e) {
        Core here = Core.withoutStanding(e);
        if (here == part) {
            return failing;
        }
        return switch (here) {
            case Core.Bool literal -> literal.value() ? Worked.UNKNOWN : Worked.FALSE;
            case Core.Read read -> bound.getOrDefault(read.binding(), Worked.UNKNOWN);
            case Core.LetIn let -> {
                if (let.binder().binding() != null) {
                    bound.put(let.binder().binding(), work(let.value()));
                }
                yield work(let.body());
            }
            case Core.Binary joined when joined.op() == BinOp.AND ->
                    work(joined.left()) == Worked.FALSE || work(joined.right()) == Worked.FALSE
                            ? Worked.FALSE : Worked.UNKNOWN;
            case Core.Binary joined when joined.op() == BinOp.OR ->
                    work(joined.left()) == Worked.FALSE && work(joined.right()) == Worked.FALSE
                            ? Worked.FALSE : Worked.UNKNOWN;
            case Core.Match match -> workMatch(match);
            case Core.PreservedCall call -> workCall(call);
            default -> Worked.UNKNOWN;
        };
    }

    /** What the lookup answers where it finds no member. */
    private static Worked answerOfNoMember(Core lookup) {
        if (!(AnOperationApplied.of(lookup) instanceof AnOperationApplied(var operation, var _))) {
            return Worked.UNKNOWN;
        }
        if (MEMBERSHIPS.contains(operation)) {
            return Worked.FALSE;
        }
        return operation.equals(GET) ? Worked.ABSENT : Worked.UNKNOWN;
    }

    /** {@code Option.map} of an absent option is absent. */
    private Worked workCall(Core.PreservedCall call) {
        if (AnOperationApplied.of(call) instanceof AnOperationApplied(var operation, var args)
                && operation.equals(ValueName.Stdlib.operation("Option", "map"))
                && args.size() == 2 && work(args.get(1)) == Worked.ABSENT) {
            return Worked.ABSENT;
        }
        return Worked.UNKNOWN;
    }

    /** A match on an absent option comes to what its arm for the absent option comes to. */
    private Worked workMatch(Core.Match match) {
        if (work(match.scrutinee()) != Worked.ABSENT) {
            return Worked.UNKNOWN;
        }
        for (Core.Case arm : match.cases()) {
            if (arm.pattern() instanceof Core.ResolvedPattern.Single one
                    && one.selected().refinement() instanceof Refinement.OptionAbsent) {
                return work(arm.body());
            }
        }
        return Worked.UNKNOWN;
    }
}
