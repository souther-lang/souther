package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The cases a subject can be selected as, worked out once from the subject's type.
 *
 * <p>A subject is one of three things and they are told apart here and nowhere else: an optional,
 * whose two carriers are the present one and the absent one; an anonymous union, whose cases are its
 * members; a named sum, whose cases are the ones declared with it. Anything else has no cases, and
 * that is an answer rather than a failure — what a reader does about a subject it cannot open is the
 * reader's ({@code E1202} for a {@code match}).
 *
 * <p>Everything a later stage needs to know about a case is on the {@link CaseSelector}: what to
 * test, and what the value is once the test answers. So a reader never asks the subject a second
 * time. That is the rule this type exists to keep — the backend used to re-derive optional-ness,
 * arity and or-pattern-ness while emitting, which is what {@code Core}'s own contract says it must
 * not do.
 *
 * <p>The selectors are ordered, in the order the subject states them. A {@code match} reads that
 * order as the order its arms are tried against, and a report reads it to list what is missing, so
 * the sequence is part of the answer and not an artefact of how it was collected.
 */
sealed interface CaseSpace {

    /** The type the cases are of. */
    Type subject();

    /** How a report names what is being selected from: {@code union `A | B`}, {@code data `X`},
     *  {@code Option}. Written here beside the cases so a diagnostic never spells it a second way. */
    String described();

    /** The cases, in the order the subject states them; empty for a subject that has none. */
    List<CaseSelector> selectors();

    /** A subject with no cases: nothing selects from it and nothing opens it. */
    record Plain(Type subject) implements CaseSpace {

        @Override
        public String described() {
            return Type.show(subject);
        }

        @Override
        public List<CaseSelector> selectors() {
            return List.of();
        }
    }

    /** A subject something can be selected from. */
    record Cases(Type subject, String described, List<CaseSelector> selectors) implements CaseSpace {

        public Cases {
            selectors = List.copyOf(selectors);
        }
    }

    /**
     * What {@code subject} can be selected as.
     *
     * <p>The one place the three forms are told apart. An optional is read before a name is, because
     * {@code Option} is not a declaration a module holds; a union is read before a name because it
     * has no name to look up.
     */
    static CaseSpace of(Type subject, Symbols symbols) {
        if (subject instanceof Type.OptionOf option) {
            return new Cases(subject, "Option", List.of(
                    new CaseSelector(TypeSymbol.SOME, new Refinement.Wrapped(option.element())),
                    new CaseSelector(TypeSymbol.NONE, new Refinement.Absent())));
        }
        if (subject instanceof Type.Union union) {
            return new Cases(subject, "union `" + Type.show(union) + "`", itself(union.members()));
        }
        if (subject instanceof Type.Ref ref
                && symbols.declarations().declaration(ref.name().key()) instanceof Hir.SumData sum) {
            return new Cases(subject, "data `" + sum.name() + "`", itself(TypeOps.caseNames(sum)));
        }
        return new Plain(subject);
    }

    /** Whether {@code name} is one of these cases. */
    default boolean holds(TypeSymbol name) {
        return selector(name) != null;
    }

    /** The case {@code name} selects, or null where it selects none of these. */
    default CaseSelector selector(TypeSymbol name) {
        for (CaseSelector selector : selectors()) {
            if (selector.name().equals(name)) {
                return selector;
            }
        }
        return null;
    }

    /** The names of these cases, in the order the subject states them. */
    default List<TypeSymbol> names() {
        List<TypeSymbol> out = new ArrayList<>();
        for (CaseSelector selector : selectors()) {
            out.add(selector.name());
        }
        return out;
    }

    /** Cases whose carrier is the value itself, de-duplicated the way the subject states them: a
     *  member written twice is one case, and the first spelling is the one the order keeps. */
    private static List<CaseSelector> itself(Iterable<TypeSymbol> members) {
        Set<TypeSymbol> seen = new LinkedHashSet<>();
        for (TypeSymbol member : members) {
            seen.add(member);
        }
        List<CaseSelector> out = new ArrayList<>();
        for (TypeSymbol member : seen) {
            out.add(new CaseSelector(member, new Refinement.Itself(TypeOps.caseBindType(member))));
        }
        return out;
    }
}
