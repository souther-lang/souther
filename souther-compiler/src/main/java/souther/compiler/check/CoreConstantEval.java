package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a checked expression comes to at compile time, read on the tree the rules are discharged
 * over.
 *
 * <p>The fold is {@link FoldedValue}'s, which the reading of an input folds with as well; this is
 * what names mean to it here. Beside {@link ConstEval} and not instead of it: the same question is
 * asked of a body where it is checked, which is {@code Hir}, and where its rules are discharged,
 * which is {@code Core}, and the two trees are two shapes. What an operator makes of the values under
 * it is neither shape's: it is {@link ConstantAlgebra}, which both ask.
 *
 * <p><b>It reads the graph rather than rebuilding a tree from it.</b> A binding is an edge, and a
 * name is followed to what it was given — from the binding standing in the tree, or from the
 * reading's own environment where the shape of the clause consumed it ({@link ClauseExpr.Scoped}).
 * Writing the value back out as syntax first and folding that is the same answer reached by copying
 * the body once per reference, which is what makes a name read twice cost twice.
 *
 * <p>Read where the name is read (ADR-0106, ADR-0111): a binding the expression never reads is
 * never folded, and a binding read more than once is folded once.
 */
final class CoreConstantEval {

    private final Symbols symbols;

    /** What the reading was told a name was given, where the binding is no longer in the tree. */
    private final Denotations at;

    /** What the values the body builds are defined as, or null where no body is read. */
    private final ValueTemplates templates;

    private CoreConstantEval(Symbols symbols, Denotations at, ValueTemplates templates) {
        this.symbols = symbols;
        this.at = at;
        this.templates = templates;
    }

    /** Folding against the library {@code symbols} names, under what {@code at} says a name was
     *  given, where no body's values are built. */
    static CoreConstantEval against(Symbols symbols, Denotations at) {
        return new CoreConstantEval(symbols, at, null);
    }

    /** The same inside a body, whose builds of a value are what {@code templates} defines them
     *  as. */
    static CoreConstantEval against(Symbols symbols, Denotations at, ValueTemplates templates) {
        return new CoreConstantEval(symbols, at, templates);
    }

    /** What {@code e} folds to, or empty where it is not a compile-time constant. */
    Optional<Object> eval(Core e) {
        Told names = new Told(templates);
        return FoldedValue.of(e, names.scope(at, Env.NONE), names, symbols);
    }

    /**
     * Where a name is read: what the reading was told the names it has met were given, and the
     * bindings the tree wrote around the read. The two travel together because a value the reading
     * was told of is read where it was told — which is not always where the name is read — and
     * under none of the bindings the tree makes around the read.
     *
     * <p>Made only by {@link Told#scope}, one for each pair of parts in one fold: what a fold
     * remembers of a name is remembered of the scope it was read in, told apart by identity, and a
     * scope made afresh at each name followed would have every read of a name look like the first —
     * a chain of names read two ways each folded once per way through it.
     */
    private record Scope(Denotations told, Env lets) {}

    /**
     * The bindings the tree wrote, innermost first, each with the environment its value was written
     * in. A value stands for the name in the environment the binding was made in (ADR-0111).
     */
    private record Env(BindingId binding, Core value, Env definedAt, Env outer) {

        static final Env NONE = new Env(null, null, null, null);

        Env with(BindingId id, Core value) {
            return new Env(id, value, this, this);
        }

        Env read(BindingId id) {
            for (Env each = this; each != null; each = each.outer()) {
                if (id.equals(each.binding())) {
                    return each;
                }
            }
            return null;
        }
    }

    /**
     * What a name means to a fold here: the value its binding in the tree gave it, read where that
     * binding was made — or what the reading was told it was given, read where nothing the tree
     * binds is in force, since it was written where the reading was told.
     *
     * <p>Two places a binding is answered from and one reading of the answer. Which of the two
     * holds it is a fact about how far the tree was rewritten before this walk met it, and not
     * about the name: a binding has one value either way. A build of a value is what it is defined
     * as, read where nothing the tree binds is in force, since a value names nothing of the body
     * that builds it.
     */
    private static final class Told implements ValueStanding.Names<Scope, Told> {

        private final ValueTemplates templates;

        /** The one scope of each pair of parts, by the identity of each. */
        private final Map<Denotations, Map<Env, Scope>> scopes = new IdentityHashMap<>();

        Told(ValueTemplates templates) {
            this.templates = templates;
        }

        /** The scope of {@code told} and {@code lets}: the same one each time they are the same
         *  two. */
        Scope scope(Denotations told, Env lets) {
            return scopes.computeIfAbsent(told, _ -> new IdentityHashMap<>())
                    .computeIfAbsent(lets, _ -> new Scope(told, lets));
        }

        @Override
        public ValueStanding.ReadThrough<Scope> taken(Core node, Scope where) {
            Core built = templates == null ? null : templates.builtBy(node);
            return built == null ? null
                    : new ValueStanding.ReadThrough<>(built, scope(where.told(), Env.NONE));
        }

        @Override
        public ValueStanding.ReadThrough<Scope> readThrough(Core.Read read, Scope where) {
            Env bound = where.lets().read(read.binding());
            if (bound != null) {
                return new ValueStanding.ReadThrough<>(bound.value(),
                        scope(where.told(), bound.definedAt()));
            }
            ValueStanding.ReadThrough<Denotations> told = where.told().givenTo(read.binding());
            return told == null ? null
                    : new ValueStanding.ReadThrough<>(told.value(), scope(told.at(), Env.NONE));
        }

        @Override
        public List<ValueStanding.ReadThrough<Scope>> alternativesOf(Core.Read read, Scope where) {
            return null;
        }

        /**
         * The scope a binding of the tree is read inside. A scope of its own each time it is
         * entered, and that is not a second fold of anything: the value it binds is read where it
         * was bound ({@link Env#definedAt}), which is a scope already made, and a name read twice
         * is found folded in the scope it was read in before its binding is entered again.
         */
        @Override
        public Scope inside(Core.LetIn li, Scope where) {
            return scope(where.told(), where.lets().with(li.binder().binding(), li.value()));
        }

        @Override
        public Told oneAtATime() {
            return this;
        }
    }
}
