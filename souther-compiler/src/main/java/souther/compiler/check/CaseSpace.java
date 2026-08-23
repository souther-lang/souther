package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.CaseSelector;
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
 */
sealed interface CaseSpace {

    /** The type the cases are of. */
    Type subject();

    /** How a report names what is being selected from: {@code union `A | B`}, {@code data `X`},
     *  {@code Option}. Written here beside the cases so a diagnostic never spells it a second way. */
    String described();

    /**
     * The cases; empty for a subject that has none.
     *
     * <p>Ordered so that two readings of one subject list them alike — a report saying what a match
     * left out reads this, and an order that came out differently each time would move a message
     * nothing about the program had changed. A sum's cases come as declared and an optional's
     * present carrier before its absent one; a union's members are a set, so what comes out is that
     * set's iteration order and no claim is made about which member was written first.
     *
     * <p>It is not the order arms are tried in. Which arm of a {@code match} takes a value is
     * decided by the order the arms are written, which is the match's and not the subject's.
     */
    List<ResolvedCase> selectors();

    /** A subject with no cases: nothing selects from it and nothing opens it. */
    record Plain(Type subject) implements CaseSpace {

        @Override
        public String described() {
            return Type.show(subject);
        }

        @Override
        public List<ResolvedCase> selectors() {
            return List.of();
        }
    }

    /**
     * An optional, whose two carriers are the present one and the absent one.
     *
     * <p>Its own arm because what may be <em>written</em> over one differs, and a reader choosing
     * those rules reads this rather than asking the subject's type a second time. Every form that
     * admits a different surface is an arm here, so gaining one is a compile error at each reader
     * that decides by form rather than a silent fall into the general reading.
     */
    record Optional(Type subject, List<ResolvedCase> selectors) implements CaseSpace {

        public Optional {
            selectors = List.copyOf(selectors);
        }

        @Override
        public String described() {
            return "Option";
        }
    }

    /** A subject whose cases are named data: a union's members, or a sum's declared cases. */
    record Cases(Type subject, String described, List<ResolvedCase> selectors) implements CaseSpace {

        public Cases {
            selectors = List.copyOf(selectors);
        }
    }

    /**
     * What {@code subject} can be selected as.
     *
     * <p>The one place the forms are told apart. An optional is read before a name is, because
     * {@code Option} is not a declaration a module holds; a union is read before a name because it
     * has no name to look up.
     */
    static CaseSpace of(Type subject, Symbols symbols) {
        if (subject instanceof Type.OptionOf option) {
            // An optional's carriers cover themselves. What `Some` holds is the element, and the
            // element's own atoms are not what an arm over an optional answers for: `Some` is the
            // case, whatever it wraps.
            return new Optional(subject, List.of(
                    new ResolvedCase(CaseSelector.optionPresent(option.element()),
                            List.of(TypeSymbol.SOME)),
                    new ResolvedCase(CaseSelector.optionAbsent(), List.of(TypeSymbol.NONE))));
        }
        if (subject instanceof Type.Union union) {
            return new Cases(subject, "union `" + Type.show(union) + "`",
                    direct(union.members(), symbols));
        }
        if (subject instanceof Type.Ref ref
                && symbols.declarations().declaration(ref.name().key()) instanceof Hir.SumData sum) {
            return new Cases(subject, "data `" + sum.name() + "`",
                    direct(TypeOps.caseNames(sum), symbols));
        }
        return new Plain(subject);
    }

    /** Whether {@code name} is one of these cases. */
    default boolean holds(TypeSymbol name) {
        return selector(name) != null;
    }

    /** The case {@code name} selects, or null where it selects none of these. */
    default ResolvedCase selector(TypeSymbol name) {
        for (ResolvedCase selected : selectors()) {
            if (selected.name().equals(name)) {
                return selected;
            }
        }
        return null;
    }

    /** The names of these cases, in the order the subject states them. */
    default List<TypeSymbol> names() {
        List<TypeSymbol> out = new ArrayList<>();
        for (ResolvedCase selected : selectors()) {
            out.add(selected.name());
        }
        return out;
    }

    /**
     * Cases whose carrier is the value itself, de-duplicated the way the subject states them: a
     * member written twice is one case, and the first spelling is the one the order keeps.
     *
     * <p>What each covers is read from what it holds and not from its name: the {@code Int} of
     * {@code Int | DivisionByZero} holds a primitive, which {@link CaseSelector#heldBy} has already
     * worked out, and a case that is a sum holds that sum and covers the leaves under it.
     */
    private static List<ResolvedCase> direct(Iterable<TypeSymbol> members, Symbols symbols) {
        Set<TypeSymbol> seen = new LinkedHashSet<>();
        for (TypeSymbol member : members) {
            seen.add(member);
        }
        List<ResolvedCase> out = new ArrayList<>();
        for (TypeSymbol member : seen) {
            CaseSelector selector = CaseSelector.direct(member);
            // A case whose name denotes no type holds nothing to descend — `Raw`, which a stage may
            // be unioned with and which no declaration takes apart — and covers no atom. The same
            // answer {@link AtomSpace} gives a type that names no case, said here because the type
            // to ask it about is the one that is missing.
            Type held = selector.bound();
            out.add(new ResolvedCase(selector,
                    held == null ? List.of() : AtomSpace.subjectAtoms(held, symbols)));
        }
        return out;
    }
}
