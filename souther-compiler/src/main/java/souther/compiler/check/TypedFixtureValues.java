package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every nullary value this module declares or imports whose body states a type one of this
 * module's own behaviors declares a parameter at, keyed by that type — the candidates a
 * class-partitioning search may offer as a baseline for a parameter of that type, before any row
 * or fake ever names one.
 *
 * <p>Narrowed to those types and not every type a nullary value happens to build: a candidate this
 * finds is minted a {@link FixtureValueEntries.Emitted fixture entry} whether or not a search ever
 * reaches for it, and {@link LoweringRole#valuesWithAnEntry} reads that entry as a reason to type the
 * value at the entry rather than at each place it is copied in — a value of a type nothing here
 * takes or answers has no reason to trade the wider typing for that, and offering it as a candidate
 * that answers no parameter would be exactly that trade for nothing.
 *
 * <p>Own {@link Hir.SpecBehavior}s and their input types, not {@code behaviors}' whole domain and
 * not output types either. {@code behaviors} is {@code Bodies.Reachable} — this module's own and
 * every one it borrows — because reading a candidate's body needs the wider table to type a call
 * the body makes of a borrowed behavior; but a borrowed behavior's own parameter is a fact about the
 * module that declares it, not this one, and offering a candidate for it is a claim this module
 * never makes. Nor is a {@link Hir.PipeBehavior}'s: {@code Adequacy.Generated.compute} only ever
 * generates rows for a {@code SpecBehavior} — {@code specOf} answers null for anything else and
 * generation stops there, its own comment saying why: {@code "A composition's inputs are its first
 * stage's and are divided there"}. Nor is a behavior's answer: {@code Adequacy.Generated.named}, the
 * search this hoists, has only ever read {@code sig.inputTypes()} — never {@code outputType()} — so
 * keeping this to a {@code SpecBehavior}'s input types is carrying that search's own domain forward
 * exactly rather than widening it along the way.
 *
 * <p>Read over {@link HelperTable#reachable} and not {@link Bodies.ModuleDefinitions}: that answer
 * is downstream of this module's own {@code CheckSurface} and asking it here would be the cycle
 * {@code Shapes.CheckSurface} already refuses. {@link HelperTable} needs none of that for the
 * module's own declarations — its own materials, {@code declared}/{@code takenOn}, are exactly what
 * a surface being assembled already holds — so this runs at assembly time and its answer is ready
 * before {@link FixtureValueEntries} mints anything.
 *
 * <p>Candidates are the module's own and every value its own import lines admit, both read off one
 * table: {@code importedForEvidence} is handed to {@link HelperTable#of} as the table's own
 * imported map, so an imported nullary value is reached under its {@link Hir.FnDef#takenOnAs()}
 * exactly the way a name an own body actually calls would be. {@code importedForEvidence} is wider
 * than the leaves an import line admits, though — {@link Bodies#publishedByQualifiedName} carries
 * every further definition a leaf's own body reaches in turn, the way {@code Bodies.ImportedDefinitions}
 * would, so that reading a candidate's declared type can read past a call the candidate's own body
 * makes of an imported helper, the way {@code let vip = of(Gold)} reads as {@code Customer} whether
 * {@code of} is this module's own or one it imports. A value only a leaf's own body reaches that
 * way — {@code base}, where an import line admits only {@code listed} and {@code listed}'s own body
 * spreads {@code base} — is not itself a candidate: {@code base} is {@code shared.people}'s to
 * name, an import line here never having admitted it, so {@code importedLeaves} — {@link
 * Bodies#importedLeaves}'s answer, the leaves an import line actually admits — is what narrows the
 * candidate loop back down to the module's own plus those, while {@code importedForEvidence} still
 * widens what {@link DeclaredTypeReading} may read a candidate's own body against.
 *
 * <p>{@link InliningPolicy#DISCHARGE} and not {@link InliningPolicy#FULL}: a candidate drawn from the
 * standard library is not a value this module's own search reasons about, and {@code FULL} is the
 * policy that pulls the library in.
 *
 * <p>What each candidate is declared to be is read by {@link DeclaredTypeReading}, the one walk every
 * other consumer of a declared type reads through — never a second, narrower one built here. Its
 * {@code values} table is keyed by spelling, so the definitions {@link HelperEntry} carries are
 * projected onto {@link HelperEntry#address()}'s text once, for that table alone; the candidate
 * itself is held by {@link HelperEntry#reachedAs()}, which is the reference a search composes a row
 * against and the reference {@link FixtureValueEntries} mints an entry under. The two are not
 * interchangeable ({@link HelperEntry}'s own doc): an imported value's address and the name a call
 * reaches it by are different strings, and asking one for what the other answers is the rediscovery
 * this exists to stop.
 *
 * <p>{@link FieldRead.Unreadable#MAKES_NOTHING_READABLE} and not {@code REFUSED}: this runs inside
 * {@link CheckSurface#assemble}, which is best-effort over a module that need not have checked yet
 * ({@code ResolvedFieldTypes} is the same choice, for the same reason). A candidate whose field is
 * not yet readable states nothing rather than raising — raising here would make discovering a
 * baseline nothing asked for the reason a whole module's surface goes missing.
 */
public final class TypedFixtureValues {

    private TypedFixtureValues() {
    }

    /**
     * The candidates {@code module} states or imports, keyed by the type each is declared to
     * build, in the order {@link HelperTable#reachable} reaches them — one of {@code module}'s own
     * {@code SpecBehavior}s' own declared input types, and no other.
     */
    public static Map<TypeSymbol, List<ReachName.Declaration>> of(Hir.Module module,
            Map<String, Hir.FnDef> importedForEvidence, Set<ValueName.Helper> importedLeaves,
            Stdlib stdlib, Symbols symbols, SumCases sums, DeclarationKinds kinds,
            NewtypeInners fieldWraps, Map<ValueName.Behavior, Sig> behaviors) {
        Set<String> generated = new LinkedHashSet<>();
        for (Hir.BehaviorDef behavior : module.behaviors()) {
            if (behavior instanceof Hir.SpecBehavior spec) {
                generated.add(spec.name());
            }
        }
        Set<TypeSymbol> relevant = new LinkedHashSet<>();
        for (Map.Entry<ValueName.Behavior, Sig> each : behaviors.entrySet()) {
            if (!each.getKey().module().equals(module.name())
                    || !generated.contains(each.getKey().name())) {
                // Borrowed rather than declared, its parameter is a fact about its own module; a
                // composition's rather than a SpecBehavior's, its input is its first stage's and
                // divided there — Adequacy.Generated never generates a row against it directly.
                continue;
            }
            for (Type type : each.getValue().inputTypes()) {
                if (type instanceof Type.Ref(TypeSymbol of)) {
                    relevant.add(of);
                }
            }
        }
        if (relevant.isEmpty()) {
            return Map.of();
        }
        // Own and imported alike: importedForEvidence is exactly the closure of what this module's
        // import lines admit, HelperTable.of's own imported branch reaches each under its
        // takenOnAs() the same way it would for a name an own body actually calls — so handing it
        // the table's imported map, rather than an empty one, is what makes an imported value a
        // candidate too, with no second reading of what "imported" means built here.
        HelperTable table = HelperTable.of(module, importedForEvidence, InliningPolicy.DISCHARGE,
                stdlib);
        Map<String, Hir.FnDef> readableBySpelling = new LinkedHashMap<>();
        for (HelperEntry entry : table.reachable().values()) {
            readableBySpelling.put(entry.address().text(), entry.definition());
        }
        DeclaredTypeReading evidence = new DeclaredTypeReading(
                new DeclarationFacts(
                        new FieldRead(symbols, sums, kinds,
                                new ResolvedFieldTypes(symbols, fieldWraps),
                                FieldRead.Unreadable.MAKES_NOTHING_READABLE),
                        DeclarationNewtypes.asWritten(symbols)),
                readableBySpelling, behaviors);
        Map<TypeSymbol, List<ReachName.Declaration>> out = new LinkedHashMap<>();
        for (HelperEntry entry : table.reachable().values()) {
            // Own, or one of the leaves an import line here actually admits — never a further
            // definition only carried in importedForEvidence so a call past it could be read
            // (this class's own doc, `base`).
            if (entry.reachedAs() instanceof ReachName.OfModule imported
                    && !importedLeaves.contains(imported.denotes())) {
                continue;
            }
            Hir.FnDef definition = entry.definition();
            if (!definition.params().isEmpty()
                    || !(definition.body() instanceof Hir.FnBody.Written written)
                    || !(evidence.declaredTypeOf(written.expr()) instanceof Type.Ref(TypeSymbol of))
                    || !relevant.contains(of)) {
                continue;
            }
            out.computeIfAbsent(of, _ -> new ArrayList<>()).add(entry.reachedAs());
        }
        return out;
    }
}
