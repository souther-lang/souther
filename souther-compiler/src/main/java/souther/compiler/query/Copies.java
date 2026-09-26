package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.CarriedDefinitions;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.InvariantSettled;
import souther.compiler.check.Lower;
import souther.compiler.check.TypeOps;
import souther.compiler.copied.CopiedIdentity;
import souther.compiler.copied.CopyRecord;
import souther.compiler.copied.CopyTarget;
import souther.compiler.types.ReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * What each module's declarations offer another module to copy into its classes, and what a module's
 * classes copied of other modules' declarations.
 *
 * <p>The copy half of what a module is built against, beside {@link Linkages}. Some of what a class
 * takes from another module's declaration is compiled into it rather than linked, and afterwards
 * nothing in the class names the declaration: a helper expanded where it is called or taken on as a
 * method, a value's constant or body written where the value is named, a type's invariant checked by
 * a type that includes it. What was copied is recorded where the copy is made ({@link
 * HelperInliner#copiedFromElsewhere}), and what it was copied as is what the declaring module offers
 * — asked of that module and made once there, so a module that copied a declaration and the module
 * that declares it cannot come to describe one copy two ways (spec
 * {@code [#a-published-module-agrees-with-what-it-copied]}).
 */
public final class Copies {

    private Copies() {}

    /**
     * What a module's declarations offer to be copied, what a copy of each takes along with it, and
     * what of other modules' declarations what they offer rests on.
     *
     * @param provides what each declaration of the module offers, by the declaration
     * @param absorbed for each declaration of the module, the declarations of other modules a copy
     *                 of it holds and does not name — a helper of a third module its closing
     *                 expanded, a value its clauses were settled with. What it offers names them,
     *                 so a reader copying it copies them as well, held to what they offer
     * @param read     each declaration of another module what the module offers rests on, and what
     *                 it was copied as — the constant of a third module one of its values folds
     *                 through, and what folding it expanded. Part of what the module is built
     *                 against, for what it offers is what a reader copies
     */
    public record Of(SortedMap<CopyTarget, CopyRecord> provides,
                     SortedMap<CopyTarget, SortedSet<CopyTarget>> absorbed,
                     SortedMap<CopyTarget, CopyRecord> read) {
        public Of {
            provides = Collections.unmodifiableSortedMap(new TreeMap<>(provides));
            SortedMap<CopyTarget, SortedSet<CopyTarget>> each = new TreeMap<>();
            absorbed.forEach((target, along) ->
                    each.put(target, Collections.unmodifiableSortedSet(new TreeSet<>(along))));
            absorbed = Collections.unmodifiableSortedMap(each);
            read = Collections.unmodifiableSortedMap(new TreeMap<>(read));
        }
    }

    /**
     * What one declaration offers to be copied, as the module that declares it provides it here.
     *
     * <p>Its own question so that a module that copied a declaration depends on that declaration and
     * on no other of its module.
     */
    public record Projection(CopyTarget target) implements Key<CopyRecord> {
        @Override
        public String module() {
            return target.module();
        }

        @Override
        public Answer<CopyRecord> compute(Db db) {
            Map<CopyTarget, CopyRecord> offered = offered(db, target.module());
            CopyRecord found = offered == null ? null : offered.get(target);
            return found == null ? Answer.absent() : Answer.of(found);
        }
    }

    /**
     * What a copy of {@code target} holds of other modules' declarations and does not name, as the
     * module that declares it works that out here.
     *
     * <p>Its own question for the reason {@link Projection} is.
     */
    public record Absorbed(CopyTarget target) implements Key<SortedSet<CopyTarget>> {
        @Override
        public String module() {
            return target.module();
        }

        @Override
        public Answer<SortedSet<CopyTarget>> compute(Db db) {
            Answer<Of> provided = db.ask(new Provided(target.module()));
            if (!provided.present()) {
                return Answer.absent();
            }
            SortedSet<CopyTarget> along = provided.value().absorbed().get(target);
            return along == null ? Answer.absent() : Answer.of(along);
        }
    }

    /**
     * What a module's declarations offer to be copied.
     *
     * <p>Each is offered closed over its own module and no other ({@link CopiedIdentity}): a helper
     * or a value as closing hands it to a reader ({@link Bodies#carrying}), a value as the constant
     * it folds to where it folds to one, and a type's invariant as its clauses closed the same way.
     * What another module's definition is enters what this module offers only as what names it, so
     * what this module offers moves with what it wrote and not with how another module's definition
     * is said — which is what lets a copy of a copy be compared by the same rule as the copy. What a
     * copy of it holds of those definitions is said beside it ({@link Of#absorbed}), and a reader
     * copies them as copies of their own. Only the module's own declarations: what closing carries
     * along of a module further up is that module's to offer.
     *
     * <p>For a module read off the path, made the same way out of what it published, and asked only
     * once the module has been held to what it was built against — its classes are what it offers,
     * and a module whose classes were built against something else offers what they offer. Held, the
     * two are the same, and that is checked: a difference is this compiler making a copy two ways.
     */
    public record Provided(String name) implements Key<Of> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null && !db.ask(new Linkages.Held(name)).present()) {
                return Answer.absent();
            }
            Answer<Hir.Module> settled = db.ask(new Bodies.Settled(name));
            Answer<Hir.Module> resolved = db.ask(new Names.Resolved(name));
            Answer<InvariantSettled> settling = db.ask(new Shapes.Settling(name));
            Answer<Bodies.Expanding.Of> against =
                    db.ask(new Bodies.Expanding(name, InliningPolicy.FULL));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            // What a module that did not check offers is not asked: a copy is written of what
            // checked, and a module that did not has said why.
            Answer<Bodies.ModuleCheck.Of> checked = db.ask(new Bodies.ModuleCheck(name));
            if (!settled.present() || !resolved.present() || !settling.present()
                    || !against.present() || !scope.present() || !checked.present()
                    || !checked.value().sound()) {
                return Answer.absent();
            }
            Hir.Module from = settled.value();
            // Everything the module hands another module's readers, and not only what it
            // publishes: a helper its invariant calls is read, and a recursive one taken on, by a
            // module whose type includes that invariant.
            Set<String> handedOver = CarriedDefinitions.of(resolved.value(), from.published());
            List<Hir.FnDef> roots = new ArrayList<>();
            for (Hir.FnDef fn : HelperInliner.helpersOf(from).values()) {
                if (fn.body() instanceof Hir.FnBody.Written && handedOver.contains(fn.name())) {
                    roots.add(fn);
                }
            }
            Bodies.Carried carried = Bodies.carrying(from, roots, against.value());
            HelperInliner folding = HelperInliner.over(against.value().table(),
                    against.value().graph()).callingValuesAsMethodsWhereEmitted(scope.value());
            SortedMap<CopyTarget, CopyRecord> provides = new TreeMap<>();
            SortedMap<CopyTarget, SortedSet<CopyTarget>> absorbed = new TreeMap<>();
            // What a constant is rests on everything folding it went through. A reader carries the
            // constant and nothing of those, so they are what this module's offer rests on.
            Set<CopyTarget> restsOn = new LinkedHashSet<>();
            CopiedIdentity.Owner owner = new CopiedIdentity.Owner(name, helper ->
                    against.value().table().reached(new ReachName.Own(helper)));
            for (Hir.FnDef def : carried.definitions().values()) {
                ValueName.Helper declared = ownDefinition(def, name);
                if (declared == null) {
                    continue;
                }
                SortedSet<CopyTarget> closing = carried.absorbed().get(def.name());
                if (def.params().isEmpty()) {
                    CopyTarget.Value target = new CopyTarget.Value(declared);
                    CopyRecord offered = CopiedIdentity.value(def,
                            folding.constantOfOwn(declared.name()), owner);
                    provides.put(target, offered);
                    if (offered.form() == CopyRecord.Form.CONSTANT) {
                        absorbed.put(target, new TreeSet<>());
                        restsOn.addAll(closing);
                    } else {
                        absorbed.put(target, closing);
                    }
                } else {
                    CopyTarget.Helper target = new CopyTarget.Helper(declared);
                    provides.put(target, CopiedIdentity.helper(def, owner));
                    absorbed.put(target, closing);
                }
            }
            HelperInliner closingClauses = HelperInliner.over(against.value().table(),
                    against.value().graph());
            for (Hir.Def def : resolved.value().defs()) {
                if (def instanceof Hir.Data data) {
                    CopyTarget.Invariant target = new CopyTarget.Invariant(data.declares().key());
                    provides.put(target, CopiedIdentity.clauses(
                            closingClauses.closeClausesAcross(data, name), owner));
                    absorbed.put(target,
                            new TreeSet<>(settling.value().copiedBy(data.declares().key())));
                }
            }
            restsOn.addAll(folding.copiedFromElsewhere());
            SortedMap<CopyTarget, CopyRecord> read = asOffered(db, restsOn);
            if (read == null) {
                return Answer.absent();
            }
            if (onThePath != null) {
                itOffersWhatItsClassesOffer(name, provides, onThePath.providedCopies());
            }
            return Answer.of(new Of(provides, absorbed, read));
        }
    }

    /** What {@code def} is a closed copy of, where it is a definition of {@code module} — or null
     *  for one closing carried along from a module further up. */
    private static ValueName.Helper ownDefinition(Hir.FnDef def, String module) {
        ReachName.Declaration reached = def.takenOnAs();
        return reached != null && reached.denotes() instanceof ValueName.Helper declared
                && declared.module().equals(module) ? declared : null;
    }

    /**
     * What the classes of a module compiled here copied of other modules' declarations, and what
     * each was copied as.
     *
     * <p>Gathered from where each copy was made: the expansions of every method the module emits
     * ({@link Lower.Lowered#copied}), the expansion of its clauses ({@link
     * InvariantSettled#copiedFromElsewhere}), and the declarations of other modules its types
     * include, whose clauses its constructions check. Then what each of those holds of further
     * declarations ({@link Absorbed}), and so on, since what a copy holds the classes carry as much
     * as the copy itself. And what its own offers rest on. A decoder checks the same clauses its
     * constructions do, expanded under a policy that differs only in the language's own
     * operations, so it copies nothing the clauses did not.
     */
    public record Required(String name) implements Key<SortedMap<CopyTarget, CopyRecord>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<SortedMap<CopyTarget, CopyRecord>> compute(Db db) {
            Answer<Lower.Lowered> lowering = db.ask(new Bodies.Lowering(name));
            Answer<InvariantSettled> settling = db.ask(new Shapes.Settling(name));
            Answer<Hir.Module> settled = db.ask(new Bodies.Settled(name));
            Answer<DerivedSymbols> scope = Names.derivedSymbols(db, name);
            Answer<Of> own = db.ask(new Provided(name));
            if (!lowering.present() || !settling.present() || !settled.present()
                    || !scope.present() || !own.present()) {
                return Answer.absent();
            }
            Set<CopyTarget> copied = new LinkedHashSet<>(lowering.value().copied());
            copied.addAll(settling.value().copiedFromElsewhere());
            for (Hir.Def def : settled.value().defs()) {
                for (TypeSymbol.AtModule governing
                        : TypeOps.declarationsGoverning(def.declares(), scope.value())) {
                    if (!governing.module().equals(name) && !governing.isDeclaredByLanguage()) {
                        copied.add(new CopyTarget.Invariant(governing.key()));
                    }
                }
            }
            // A copy holds what the declaration it is of absorbed, and so on down: each of those is
            // copied here as much as the declaration that absorbed it is.
            Set<CopyTarget> along = new LinkedHashSet<>();
            Deque<CopyTarget> pending = new ArrayDeque<>(copied);
            while (!pending.isEmpty()) {
                CopyTarget target = pending.poll();
                if (!along.add(target)) {
                    continue;
                }
                Answer<SortedSet<CopyTarget>> absorbed = db.ask(new Absorbed(target));
                if (!absorbed.present()) {
                    return Answer.absent();
                }
                pending.addAll(absorbed.value());
            }
            SortedMap<CopyTarget, CopyRecord> out = asOffered(db, along);
            if (out == null) {
                return Answer.absent();
            }
            own.value().read().forEach((target, record) -> {
                CopyRecord already = out.putIfAbsent(target, record);
                if (already != null && !already.equals(record)) {
                    throw new IllegalStateException(target.shown() + " is copied two ways in "
                            + name);
                }
            });
            return Answer.of(Collections.unmodifiableSortedMap(out));
        }
    }

    /**
     * Each of {@code copied} as its declaring module offers it — or null where one of those modules
     * offers nothing here, which is said where that module is found.
     *
     * <p>Asked one declaration at a time, so what copied a declaration depends on that declaration
     * and not on the rest of its module.
     */
    private static SortedMap<CopyTarget, CopyRecord> asOffered(Db db, Set<CopyTarget> copied) {
        SortedMap<CopyTarget, CopyRecord> out = new TreeMap<>();
        for (CopyTarget target : copied) {
            Answer<CopyRecord> record = db.ask(new Projection(target));
            if (!record.present()) {
                if (offered(db, target.module()) == null) {
                    return null;
                }
                // What was copied was reached through the declaring module's own table, so it is a
                // declaration that module has; one it does not offer is two answers here to what a
                // module offers to be copied.
                throw new IllegalStateException(target.shown() + " was copied and its module offers"
                        + " no " + target.kind() + " of that name");
            }
            out.put(target, record.value());
        }
        return out;
    }

    /**
     * What {@code module} offers to be copied, as a module built against it copied it: as its classes
     * record it, for a module off the path, and as its classes are about to offer it, for one compiled
     * here — or null where this compilation does not have it, or it did not come out.
     */
    static Map<CopyTarget, CopyRecord> offered(Db db, String module) {
        Front.FromPath.OnThePath onThePath = Front.onThePath(db, module);
        if (onThePath != null) {
            return onThePath.providedCopies();
        }
        List<String> declared = db.ask(new Front.Declared()).value();
        if (declared == null || !declared.contains(module)) {
            return null;
        }
        Answer<Of> provided = db.ask(new Provided(module));
        return provided.present() ? provided.value().provides() : null;
    }

    /**
     * That what this compiler works out a module off the path offers to be copied is what its
     * classes record they offer — asked of a module already held to what it was built against, for
     * the reason {@link Linkages} asks it of a projection.
     */
    private static void itOffersWhatItsClassesOffer(String name,
                                                    Map<CopyTarget, CopyRecord> workedOut,
                                                    Map<CopyTarget, CopyRecord> recorded) {
        if (workedOut.equals(recorded)) {
            return;
        }
        List<String> differing = new ArrayList<>();
        Set<CopyTarget> targets = new LinkedHashSet<>(new TreeMap<>(recorded).keySet());
        targets.addAll(new TreeMap<>(workedOut).keySet());
        for (CopyTarget target : targets) {
            CopyRecord was = recorded.get(target);
            CopyRecord now = workedOut.get(target);
            if (was == null || now == null) {
                differing.add(target.shown() + (was == null ? " is not recorded"
                        : " is recorded and not worked out"));
            } else if (!was.equals(now)) {
                differing.add(target.shown() + ": its " + was.form().written() + " differs");
            }
        }
        throw new IllegalStateException("what " + name + " offers to be copied was worked out"
                + " otherwise than its classes record it: " + differing);
    }
}
