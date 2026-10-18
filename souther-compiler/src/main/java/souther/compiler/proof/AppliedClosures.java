package souther.compiler.proof;

import souther.compiler.ast.Hir;
import souther.compiler.core.TheWalk;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;

/**
 * Which closure each operation the library defines in the language hands what a container holds,
 * and how far it goes, read off its body.
 *
 * <p>A signature says a closure could be handed an element. Whether it is, which container the
 * element comes from, and how far the operation goes are what the body does, and are read here by
 * a few rules, each a step a body takes:
 * <ul>
 *     <li>the walk hands its step every element of its list from the index it is handed, which its
 *     own body says ({@link TheWalk});</li>
 *     <li>an operation handing its closure on, as the closure of an operation already read, hands
 *     it what that one does;</li>
 *     <li>an operation applying its closure inside a closure it hands another applies it to what
 *     that one hands, on every run of the inner closure where nothing chooses around the
 *     application;</li>
 *     <li>where the inner closure is the step of a walk from {@code false} that answers what it
 *     carries or the application, the application is made until one holds, and from {@code true}
 *     with "and", until one fails;</li>
 *     <li>where the closure is applied to the value an option holds, and the option is what a kernel
 *     answers holding at most one element of a container, it is applied to at most that one;</li>
 *     <li>where it is applied inside a walk's step beside the element to a part of what the walk
 *     carries that starts at nought and that every step answers one more of, it is handed the
 *     element's position there ({@link #counting}).</li>
 * </ul>
 * A container reached through a kernel counts as that kernel's argument where the kernel is
 * declared to list every element of it ({@link Listings}). Anything else applies its closure in no
 * way read here, and nothing is said of it.
 *
 * <p>An operation applying a closure in a body this reads before the one it hands it on to is read
 * later: the order the library declares its operations in is no order the rules depend on.
 */
public final class AppliedClosures {

    /**
     * What a kernel's answer lists of its arguments, as it is declared of the kernel.
     *
     * <p>Handed over rather than asked of the declarations here, since what a kernel answers is an
     * axiom about it and lives where those are bound.
     */
    @FunctionalInterface
    public interface Listings {

        /** What {@code operation}'s answer lists, or null where it is declared to list nothing. */
        Listing of(ValueName.Stdlib.Operation operation);
    }

    /** What an answer lists of an argument. */
    public sealed interface Listing {

        /**
         * Every element the argument at {@code argument} holds, each once — and no two of them
         * the same value, where {@code eachDifferent}, as the elements of a set are.
         */
        record EveryElementOf(int argument, boolean eachDifferent) implements Listing {}

        /** Every entry of the map at {@code argument}, each once, as a pair of its key and value —
         *  no two of them under the same key. */
        record EveryEntryOf(int argument) implements Listing {}

        /** At most one element the argument at {@code argument} holds. */
        record AtMostOneElementOf(int argument) implements Listing {}
    }

    private final Stdlib library;
    private final Listings listings;
    private final Function<ValueName.Stdlib.Operation, ClosurePositions> positions;
    private final Map<ValueName.Stdlib.Operation, Combinator> known;
    /** The operations whose bodies are not read yet. */
    private final Set<ValueName.Stdlib.Operation> waiting;

    private AppliedClosures(Stdlib library, Listings listings,
                            Function<ValueName.Stdlib.Operation, ClosurePositions> positions,
                            Map<ValueName.Stdlib.Operation, Combinator> known,
                            Set<ValueName.Stdlib.Operation> waiting) {
        this.library = library;
        this.listings = listings;
        this.positions = positions;
        this.known = known;
        this.waiting = waiting;
    }

    /**
     * What every operation of {@code library} applies its closure to, as far as it is read: the
     * kernels as {@code kernels} declares, and every operation with a body as that body says.
     *
     * @param positions where each operation's signature puts its closure and container; an
     *                  operation whose body hands its closure something in other places than
     *                  these is a library at odds with itself, and is refused
     */
    public static Map<ValueName.Stdlib.Operation, Combinator> of(
            Stdlib library, Map<ValueName.Stdlib.Operation, Combinator> kernels,
            Listings listings, Function<ValueName.Stdlib.Operation, ClosurePositions> positions) {
        Map<ValueName.Stdlib.Operation, Combinator> known = new LinkedHashMap<>(kernels);
        TheWalk walk = library.walk();
        known.put(walk.operation(), new Combinator(walk.step(), walk.element(), walk.container(),
                Combinator.NO_KEY, Combinator.NO_POSITION, HowAClosureIsApplied.TO_EVERY_ELEMENT,
                walk.index()));
        Set<ValueName.Stdlib.Operation> waiting = new LinkedHashSet<>();
        library.helpers().keySet().forEach(operation -> {
            if (!known.containsKey(operation)) {
                waiting.add(operation);
            }
        });
        AppliedClosures reading = new AppliedClosures(library, listings, positions, known,
                waiting);
        boolean read = true;
        while (read) {
            read = false;
            for (ValueName.Stdlib.Operation operation : List.copyOf(waiting)) {
                Read answer = reading.read(operation);
                if (answer instanceof Read.Waits) {
                    continue;
                }
                waiting.remove(operation);
                read = true;
                if (answer instanceof Read.Applies(Combinator rule)) {
                    reading.held(operation, rule);
                    known.put(operation, rule);
                }
            }
        }
        if (!waiting.isEmpty()) {
            throw new IllegalStateException("what " + waiting + " apply their closures waits on one"
                    + " another, so none of it is read");
        }
        library.rewrites().forEach((sugar, rewrite) -> {
            Combinator target = known.get(rewrite.target());
            Combinator rule = target == null ? null : sugared(target, rewrite);
            if (rule != null) {
                known.put(sugar, rule);
            }
        });
        return Map.copyOf(known);
    }

    /** What a sugar of {@code target} applies: the same, where the arguments it supplies leave the
     *  first element where the target starts. */
    private static Combinator sugared(Combinator target, Stdlib.Rewrite rewrite) {
        List<Integer> placed = rewrite.arguments(
                IntStream.range(0, rewrite.keptArgs()).boxed().toList(), constant -> constant);
        if (target.closureArg() >= rewrite.keptArgs() || target.containerArg() >= rewrite.keptArgs()) {
            return null;
        }
        int startsFrom = target.startsFrom();
        if (startsFrom != Combinator.FROM_THE_FIRST) {
            if (startsFrom < rewrite.keptArgs()) {
                return target;
            }
            if (placed.get(startsFrom) != 0) {
                return null;
            }
            startsFrom = Combinator.FROM_THE_FIRST;
        }
        return new Combinator(target.closureArg(), target.elementParam(), target.containerArg(),
                target.keyParam(), target.positionParam(), target.applied(), startsFrom);
    }

    /** {@code rule}, read off the body of {@code operation}, held to where its signature puts the
     *  closure and the container. */
    private void held(ValueName.Stdlib.Operation operation, Combinator rule) {
        ClosurePositions signature = positions.apply(operation);
        if (!rule.positions().equals(signature)) {
            throw new IllegalStateException("the body of " + operation + " hands its closure "
                    + rule.positions() + " and its signature puts them at " + signature);
        }
    }

    /** What reading one body came to. */
    private sealed interface Read {

        /** The body applies its closure as {@code rule} says. */
        record Applies(Combinator rule) implements Read {}

        /** The body applies its closure in no way read here, or has none. */
        record Nothing() implements Read {}

        /** The body hands its closure to an operation not read yet. */
        record Waits() implements Read {}
    }

    private Read read(ValueName.Stdlib.Operation operation) {
        Stdlib.Entry entry = library.entry(operation);
        List<Type> params = entry.signature().params();
        int closure = -1;
        for (int at = 0; at < params.size(); at++) {
            if (params.get(at) instanceof Type.FnOf) {
                if (closure >= 0) {
                    return new Read.Nothing();
                }
                closure = at;
            }
        }
        if (closure < 0) {
            return new Read.Nothing();
        }
        Hir.FnDef declaration = library.helpers().get(operation);
        Walking walking = new Walking(closure);
        walking.walk(LibraryTerms.of(library, declaration), new Scope(Map.of(), null), true);
        if (walking.waits) {
            return new Read.Waits();
        }
        return walking.rule().<Read>map(Read.Applies::new).orElseGet(Read.Nothing::new);
    }

    /**
     * Where an element a closure is handed came from: an argument of the operation, how many of
     * what it holds are handed, and whether they are walked in the order the argument holds them —
     * which a listing a kernel answers of it is not shown to keep.
     */
    private record Source(int argument, boolean everyOne, boolean inItsOrder) {}

    /** What a value bound inside a body is, as far as these rules care. */
    private sealed interface Role {

        /** An element of {@code from}, handed to the step {@code step} of a walk over it — null
         *  where no step was handed it, as the value an option holds is not. */
        record Element(Source from, LibraryTerm.Closure step) implements Role {}

        record Key(Source from) implements Role {}

        record Entry(Source from) implements Role {}

        /**
         * What a walk from {@code seed} over {@code from} carries, inside its step {@code step},
         * with the components of it that count the elements walked before the one that step is
         * handed ({@link #counting}) — none where the walk is over no argument.
         */
        record Carried(LibraryTerm seed, Set<Integer> counting, Source from,
                       LibraryTerm.Closure step) implements Role {}

        /**
         * Where the element the step {@code step} is handed stands in {@code from}, counted from
         * nought.
         *
         * <p>Of that step's element and of no other: a walk nested in the step hands elements of
         * its own, of the same list it may be, at the one position the outer element stands at.
         */
        record Position(Source from, LibraryTerm.Closure step) implements Role {}
    }

    /**
     * The roles of what is bound around a place, and how far the closure the place is inside is
     * applied — null outside every closure handed to an operation.
     */
    private record Scope(Map<BindingId, Role> roles, HowAClosureIsApplied enclosing) {

        Scope with(BindingId binding, Role role) {
            Map<BindingId, Role> more = new HashMap<>(roles);
            more.put(binding, role);
            return new Scope(more, enclosing);
        }
    }

    /** One place the closure is applied or handed on, with what each argument is there. */
    private record Site(Combinator rule, boolean always) {}

    /** One walk over one body, gathering where the closure at {@code closure} goes. */
    private final class Walking {

        private final int closure;
        private final List<Site> sites = new ArrayList<>();
        private boolean waits;
        private boolean unread;

        Walking(int closure) {
            this.closure = closure;
        }

        /**
         * What the sites come to. Where the closure is handed is the same at every site, or nothing
         * is said. How far it is applied is said by a site the inner closure reaches on every run,
         * every other site applying it again to the same element; where none is reached on every
         * run, by the one site applying it to at most one element; and otherwise it is applied to
         * some of them, which is all that is said.
         *
         * <p>The element's position is said only where every site hands it at the same parameter.
         * A site handing the element where another hands it beside its position leaves that
         * parameter something else on some application, and the element is still the element.
         */
        Optional<Combinator> rule() {
            if (unread || sites.isEmpty()) {
                return Optional.empty();
            }
            Combinator first = sites.get(0).rule();
            int position = first.positionParam();
            for (Site site : sites) {
                if (!site.rule().positions().equals(first.positions())) {
                    return Optional.empty();
                }
                if (site.rule().positionParam() != position) {
                    position = Combinator.NO_POSITION;
                }
            }
            for (Site site : sites) {
                if (site.always()) {
                    return Optional.of(atPosition(site.rule(), position));
                }
            }
            if (sites.size() == 1 && first.applied() == HowAClosureIsApplied.AT_MOST_ONE) {
                return Optional.of(first);
            }
            return Optional.of(new Combinator(first.closureArg(), first.elementParam(),
                    first.containerArg(), first.keyParam(), position, HowAClosureIsApplied.TO_SOME,
                    Combinator.FROM_THE_FIRST));
        }

        /** {@code rule} with the element's position at {@code position}. */
        private static Combinator atPosition(Combinator rule, int position) {
            return new Combinator(rule.closureArg(), rule.elementParam(), rule.containerArg(),
                    rule.keyParam(), position, rule.applied(), rule.startsFrom());
        }

        private boolean isTheClosure(LibraryTerm term) {
            return term instanceof LibraryTerm.Parameter(int position) && position == closure;
        }

        void walk(LibraryTerm term, Scope scope, boolean always) {
            switch (term) {
                case LibraryTerm.Call call -> called(call, scope, always);
                case LibraryTerm.Applied applied -> {
                    if (isTheClosure(applied.function())) {
                        appliedHere(applied, scope, always);
                    } else {
                        walk(applied.function(), scope, always);
                    }
                    applied.args().forEach(arg -> walk(arg, scope, always));
                }
                case LibraryTerm.Parameter _ -> {
                    if (isTheClosure(term)) {
                        unread = true;   // handed somewhere no rule here follows it
                    }
                }
                case LibraryTerm.Fork fork -> {
                    walk(fork.condition(), scope, always);
                    walk(fork.then(), scope, false);
                    walk(fork.otherwise(), scope, false);
                }
                case LibraryTerm.OnAnOption on -> {
                    walk(on.option(), scope, always);
                    Scope inside = scope;
                    if (on.option() instanceof LibraryTerm.Call call
                            && listings.of(call.operation())
                                    instanceof Listing.AtMostOneElementOf(int argument)
                            && argument < call.args().size()) {
                        Source from = sourceOf(call.args().get(argument));
                        if (from != null) {
                            inside = scope.with(on.value(), new Role.Element(
                                    new Source(from.argument(), false, false), null));
                        }
                    }
                    walk(on.present(), inside, false);
                    walk(on.absent(), scope, false);
                }
                case LibraryTerm.Operator operator -> {
                    walk(operator.left(), scope, always);
                    boolean shortCircuits = operator.op() == BinOp.AND || operator.op() == BinOp.OR;
                    walk(operator.right(), scope, always && !shortCircuits);
                }
                case LibraryTerm.Let let -> {
                    walk(let.value(), scope, always);
                    Role role = roleOf(let.value(), scope);
                    walk(let.body(), role == null ? scope : scope.with(let.binding(), role),
                            always);
                }
                case LibraryTerm.Closure inner -> walk(inner.body(), scope, false);
                case LibraryTerm.ListOf list -> list.elements().forEach(e -> walk(e, scope, always));
                case LibraryTerm.TupleOf tuple ->
                        tuple.elements().forEach(e -> walk(e, scope, always));
                case LibraryTerm.Component component -> walk(component.tuple(), scope, always);
                case LibraryTerm.Negated negated -> walk(negated.operand(), scope, always);
                case LibraryTerm.Unread _ -> unread = true;
                case LibraryTerm.Bound _, LibraryTerm.WholeNumber _, LibraryTerm.DecimalNumber _,
                     LibraryTerm.Truth _ -> { }
            }
        }

        /** A call: its closure argument handed on or written out here, and the rest walked. */
        private void called(LibraryTerm.Call call, Scope scope, boolean always) {
            Combinator applies = known.get(call.operation());
            boolean mentions = call.args().stream().anyMatch(this::mentions);
            if (applies == null && mentions && waiting.contains(call.operation())) {
                waits = true;
                return;
            }
            for (int at = 0; at < call.args().size(); at++) {
                LibraryTerm arg = call.args().get(at);
                if (applies == null || at != applies.closureArg() || !startsAtTheFirst(applies, call)) {
                    walk(arg, scope, always);
                    continue;
                }
                Source from = applies.containerArg() < call.args().size()
                        ? sourceOf(call.args().get(applies.containerArg())) : null;
                Source entries = applies.containerArg() < call.args().size()
                        ? entriesOf(call.args().get(applies.containerArg())) : null;
                if (isTheClosure(arg)) {
                    if (from == null || !from.everyOne()) {
                        unread = true;
                    } else {
                        // A position in what the operation walks is one in the argument only
                        // where the one is the other as it stands.
                        sites.add(new Site(new Combinator(closure, applies.elementParam(),
                                from.argument(), applies.keyParam(),
                                from.inItsOrder() ? applies.positionParam()
                                        : Combinator.NO_POSITION,
                                applies.applied(), Combinator.FROM_THE_FIRST), always));
                    }
                } else if (arg instanceof LibraryTerm.Closure inner) {
                    Scope inside = new Scope(scope.roles(), applies.applied());
                    if (applies.elementParam() < inner.params().size()) {
                        BindingId element = inner.params().get(applies.elementParam());
                        if (from != null) {
                            inside = inside.with(element, new Role.Element(from, inner));
                        } else if (entries != null) {
                            inside = inside.with(element, new Role.Entry(entries));
                        }
                    }
                    if (applies.handsAKey() && applies.keyParam() < inner.params().size()
                            && from != null) {
                        inside = inside.with(inner.params().get(applies.keyParam()),
                                new Role.Key(from));
                    }
                    // An operation handing its closure the position hands it to this one, of the
                    // argument where that is the container as it stands.
                    if (applies.handsAPosition() && applies.positionParam() < inner.params().size()
                            && from != null && from.inItsOrder()) {
                        inside = inside.with(inner.params().get(applies.positionParam()),
                                new Role.Position(from, inner));
                    }
                    TheWalk walk = library.walk();
                    if (call.operation().equals(walk.operation())
                            && walk.accumulator() < inner.params().size()) {
                        BindingId carried = inner.params().get(walk.accumulator());
                        LibraryTerm seed = call.args().get(walk.seed());
                        inside = inside.with(carried, new Role.Carried(seed,
                                from == null ? Set.of() : counting(inner, carried, seed), from,
                                inner));
                    }
                    stopping(inner, inside);
                    walk(inner.body(), inside, true);
                } else {
                    walk(arg, scope, always);
                }
            }
        }

        /**
         * A step that answers what it carries joined with the application, inside a walk from the
         * truth that join leaves alone: the application is made until it decides the join.
         */
        private void stopping(LibraryTerm.Closure step, Scope inside) {
            if (!(step.body() instanceof LibraryTerm.Operator(BinOp op, LibraryTerm.Bound carried,
                    LibraryTerm.Applied applied, var _))
                    || (op != BinOp.OR && op != BinOp.AND)
                    || !isTheClosure(applied.function())
                    || !(inside.roles().get(carried.binding())
                            instanceof Role.Carried(LibraryTerm.Truth(boolean seed), var _, var _,
                                    var _))
                    || inside.enclosing() != HowAClosureIsApplied.TO_EVERY_ELEMENT) {
                return;
            }
            boolean or = op == BinOp.OR;
            if (seed == or) {
                return;   // a walk from the truth the join decides decides nothing more
            }
            Combinator rule = applying(applied, inside);
            if (rule != null) {
                sites.add(new Site(new Combinator(rule.closureArg(), rule.elementParam(),
                        rule.containerArg(), rule.keyParam(), rule.positionParam(),
                        or ? HowAClosureIsApplied.UNTIL_ONE_HOLDS
                                : HowAClosureIsApplied.UNTIL_ONE_FAILS,
                        Combinator.FROM_THE_FIRST), true));
            }
        }

        /** The closure applied here, to what its arguments are. */
        private void appliedHere(LibraryTerm.Applied applied, Scope scope, boolean always) {
            Combinator rule = applying(applied, scope);
            if (rule == null) {
                unread = true;
                return;
            }
            if (rule.applied() == HowAClosureIsApplied.AT_MOST_ONE) {
                sites.add(new Site(rule, true));
            } else {
                sites.add(new Site(rule, always));
            }
        }

        /** Where the element, the key and the element's position are among {@code applied}'s
         *  arguments, and how far the closure is applied there — null where no argument is an
         *  element. */
        private Combinator applying(LibraryTerm.Applied applied, Scope scope) {
            int element = -1;
            int key = Combinator.NO_KEY;
            Source from = null;
            LibraryTerm.Closure handedBy = null;
            List<Integer> positions = new ArrayList<>();
            Role.Position counted = null;
            for (int at = 0; at < applied.args().size(); at++) {
                Role role = roleOf(applied.args().get(at), scope);
                if (role instanceof Role.Element(Source source, LibraryTerm.Closure step)
                        && element < 0) {
                    element = at;
                    from = source;
                    handedBy = step;
                } else if (role instanceof Role.Key(Source source) && key == Combinator.NO_KEY) {
                    key = at;
                    if (from == null) {
                        from = source;
                    }
                } else if (role instanceof Role.Position position) {
                    positions.add(at);
                    counted = position;
                }
            }
            if (element < 0 || from == null) {
                return null;
            }
            HowAClosureIsApplied how = !from.everyOne() ? HowAClosureIsApplied.AT_MOST_ONE
                    : scope.enclosing();
            if (how == null) {
                return null;
            }
            // The position of the very element handed beside it — handed to the one step, in the
            // argument as it stands — and at one parameter: two would leave which one a reader
            // asks a question of the closure's own. The step is the step itself and not one
            // spelled alike, so it is asked by identity.
            int position = positions.size() == 1 && handedBy != null
                    && counted.step() == handedBy && from.equals(counted.from())
                    && from.inItsOrder() ? positions.getFirst() : Combinator.NO_POSITION;
            return new Combinator(closure, element, from.argument(), key, position, how,
                    Combinator.FROM_THE_FIRST);
        }

        /** What {@code value} is, where it is an element, a key, an entry, what a walk carries or
         *  the position of the element its step is handed. */
        private Role roleOf(LibraryTerm value, Scope scope) {
            return switch (value) {
                case LibraryTerm.Bound(BindingId binding) -> scope.roles().get(binding);
                case LibraryTerm.Component(LibraryTerm.Bound(BindingId binding), int index)
                        when scope.roles().get(binding) instanceof Role.Entry(Source from) ->
                        index == 0 ? new Role.Key(from)
                                : index == 1 ? new Role.Element(from, null) : null;
                case LibraryTerm.Component(LibraryTerm.Bound(BindingId binding), int index)
                        when scope.roles().get(binding)
                                instanceof Role.Carried(var _, Set<Integer> counting, Source from,
                                        LibraryTerm.Closure step)
                        && counting.contains(index) -> new Role.Position(from, step);
                default -> null;
            };
        }

        /** Whether the closure is among what {@code term} mentions. */
        private boolean mentions(LibraryTerm term) {
            return switch (term) {
                case LibraryTerm.Parameter _ -> isTheClosure(term);
                case LibraryTerm.Call call -> call.args().stream().anyMatch(this::mentions);
                case LibraryTerm.Applied applied -> mentions(applied.function())
                        || applied.args().stream().anyMatch(this::mentions);
                case LibraryTerm.Closure inner -> mentions(inner.body());
                case LibraryTerm.Let let -> mentions(let.value()) || mentions(let.body());
                case LibraryTerm.Fork fork -> mentions(fork.condition()) || mentions(fork.then())
                        || mentions(fork.otherwise());
                case LibraryTerm.OnAnOption on -> mentions(on.option()) || mentions(on.present())
                        || mentions(on.absent());
                case LibraryTerm.Operator operator -> mentions(operator.left())
                        || mentions(operator.right());
                case LibraryTerm.ListOf list -> list.elements().stream().anyMatch(this::mentions);
                case LibraryTerm.TupleOf tuple -> tuple.elements().stream().anyMatch(this::mentions);
                case LibraryTerm.Component component -> mentions(component.tuple());
                case LibraryTerm.Negated negated -> mentions(negated.operand());
                case LibraryTerm.Bound _, LibraryTerm.WholeNumber _, LibraryTerm.DecimalNumber _,
                     LibraryTerm.Truth _, LibraryTerm.Unread _ -> false;
            };
        }
    }

    /** Whether a call of an operation that starts from an index it is handed starts from the first. */
    private static boolean startsAtTheFirst(Combinator applies, LibraryTerm.Call call) {
        return applies.startsFrom() == Combinator.FROM_THE_FIRST
                || (applies.startsFrom() < call.args().size()
                && call.args().get(applies.startsFrom()) instanceof LibraryTerm.WholeNumber(long n)
                && n == 0);
    }

    /** The argument of the operation whose every element {@code container} holds, each once — or
     *  null where it is none. */
    private Source sourceOf(LibraryTerm container) {
        if (container instanceof LibraryTerm.Parameter(int position)) {
            return new Source(position, true, true);
        }
        if (container instanceof LibraryTerm.Call call
                && listings.of(call.operation()) instanceof Listing.EveryElementOf(int argument,
                        var _)
                && argument < call.args().size()) {
            Source listed = sourceOf(call.args().get(argument));
            return listed == null ? null : new Source(listed.argument(), listed.everyOne(), false);
        }
        return null;
    }

    /**
     * The components of what a walk from {@code seed} carries that count the elements it has
     * walked: nought in the seed, and one more in every answer of the step than in what the step
     * was handed at {@code carried}.
     *
     * <p>By induction over the walk, which hands its step every element of its list once each in
     * order from the first ({@link TheWalk}): such a component is, inside the step, how many
     * elements came before the one the step is handed — and so what the step reads of it before
     * it answers is that element's position. What the step answers is the next count, and is not.
     */
    private static Set<Integer> counting(LibraryTerm.Closure step, BindingId carried,
                                         LibraryTerm seed) {
        if (!(seed instanceof LibraryTerm.TupleOf(List<LibraryTerm> starts))) {
            return Set.of();
        }
        Set<Integer> out = new LinkedHashSet<>();
        for (int at = 0; at < starts.size(); at++) {
            if (starts.get(at) instanceof LibraryTerm.WholeNumber(long start) && start == 0
                    && answersOneMore(step.body(), at, carried, new HashMap<>())) {
                out.add(at);
            }
        }
        return Set.copyOf(out);
    }

    /**
     * Whether {@code answer}, on every way through it, is a tuple whose component {@code at} is
     * one more than the same component of what {@code carried} holds — reading a name it bound on
     * the way as what it was bound to.
     */
    private static boolean answersOneMore(LibraryTerm answer, int at, BindingId carried,
                                          Map<BindingId, LibraryTerm> bound) {
        return switch (answer) {
            case LibraryTerm.Let let -> {
                bound.put(let.binding(), let.value());
                yield answersOneMore(let.body(), at, carried, bound);
            }
            // Each way through with the names bound on it and on no other.
            case LibraryTerm.Fork fork ->
                    answersOneMore(fork.then(), at, carried, new HashMap<>(bound))
                            && answersOneMore(fork.otherwise(), at, carried, new HashMap<>(bound));
            case LibraryTerm.OnAnOption on ->
                    answersOneMore(on.present(), at, carried, new HashMap<>(bound))
                            && answersOneMore(on.absent(), at, carried, new HashMap<>(bound));
            case LibraryTerm.Bound(BindingId binding) when bound.containsKey(binding) ->
                    answersOneMore(bound.get(binding), at, carried, bound);
            case LibraryTerm.TupleOf(List<LibraryTerm> parts) -> at < parts.size()
                    && parts.get(at) instanceof LibraryTerm.Operator(BinOp op, LibraryTerm left,
                            LibraryTerm right, var _)
                    && op == BinOp.ADD
                    && ((isOne(right) && isTheComponent(left, at, carried, bound))
                            || (isOne(left) && isTheComponent(right, at, carried, bound)));
            default -> false;
        };
    }

    private static boolean isOne(LibraryTerm term) {
        return term instanceof LibraryTerm.WholeNumber(long n) && n == 1;
    }

    /** Whether {@code term} is the component {@code at} of what {@code carried} holds, through the
     *  names it was bound under. */
    private static boolean isTheComponent(LibraryTerm term, int at, BindingId carried,
                                          Map<BindingId, LibraryTerm> bound) {
        LibraryTerm read = followed(term, bound);
        return read instanceof LibraryTerm.Component(LibraryTerm tuple, int index) && index == at
                && followed(tuple, bound) instanceof LibraryTerm.Bound(BindingId binding)
                && binding.equals(carried);
    }

    /** {@code term} with every name on the way read as what it was bound to. */
    private static LibraryTerm followed(LibraryTerm term, Map<BindingId, LibraryTerm> bound) {
        LibraryTerm at = term;
        Set<BindingId> met = new HashSet<>();
        while (at instanceof LibraryTerm.Bound(BindingId binding) && bound.containsKey(binding)
                && met.add(binding)) {
            at = bound.get(binding);
        }
        return at;
    }

    /** The map argument of the operation whose every entry {@code container} holds, each once — or
     *  null where it is none. */
    private Source entriesOf(LibraryTerm container) {
        if (container instanceof LibraryTerm.Call call
                && listings.of(call.operation()) instanceof Listing.EveryEntryOf(int argument)
                && argument < call.args().size()
                && call.args().get(argument) instanceof LibraryTerm.Parameter(int position)) {
            return new Source(position, true, false);
        }
        return null;
    }
}
