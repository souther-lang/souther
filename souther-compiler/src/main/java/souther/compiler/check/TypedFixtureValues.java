package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Every nullary value this module reaches whose body states a type, keyed by that type — the
 * candidates a class-partitioning search may offer as a baseline for a parameter of that type,
 * before any row or fake ever names one.
 *
 * <p>Read over {@link HelperTable#reachable} and not {@link Bodies.ModuleDefinitions}: that answer
 * is downstream of this module's own {@code CheckSurface} and asking it here would be the cycle
 * {@code Shapes.CheckSurface} already refuses. {@link HelperTable} needs none of that for the
 * module's own declarations — its own materials, {@code declared}/{@code takenOn}, are exactly what
 * a surface being assembled already holds — so this runs at assembly time and its answer is ready
 * before {@link FixtureValueEntries} mints anything.
 *
 * <p>{@code importedDefinitions} is the same shape as {@link Bodies.ImportedDefinitions}'s answer,
 * but {@code Shapes.CheckSurface} currently hands this {@code Map.of()} rather than asking that key:
 * it too is downstream of this same {@code CheckSurface} (its own closure needs {@code
 * Shapes.ClausesTakenIn}), the identical cycle by a route one step longer. So today every candidate
 * this finds is the module's own; widening it to what a module imports needs a source for that
 * table which does not run through this assembly, not a change here.
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
 */
public final class TypedFixtureValues {

    private TypedFixtureValues() {
    }

    /**
     * The candidates {@code module} states, keyed by the type each is declared to build, in the
     * order {@link HelperTable#reachable} reaches them.
     */
    public static Map<TypeSymbol, List<ReachName.Declaration>> of(Hir.Module module,
            Map<String, Hir.FnDef> importedDefinitions, Stdlib stdlib, Symbols symbols,
            PublishedDeclarations published, DeclarationKinds kinds, NewtypeInners fieldWraps,
            Map<ValueName.Behavior, Sig> behaviors) {
        HelperTable table = HelperTable.of(module, importedDefinitions, InliningPolicy.DISCHARGE,
                stdlib);
        Map<String, Hir.FnDef> readableBySpelling = new LinkedHashMap<>();
        for (HelperEntry entry : table.reachable().values()) {
            readableBySpelling.put(entry.address().text(), entry.definition());
        }
        DeclaredTypeReading evidence = new DeclaredTypeReading(
                new DeclarationFacts(
                        new FieldRead(symbols, published, kinds,
                                new ResolvedFieldTypes(symbols, fieldWraps),
                                FieldRead.Unreadable.REFUSED),
                        DeclarationNewtypes.asWritten(symbols)),
                readableBySpelling, behaviors);
        Map<TypeSymbol, List<ReachName.Declaration>> out = new LinkedHashMap<>();
        for (HelperEntry entry : table.reachable().values()) {
            Hir.FnDef definition = entry.definition();
            if (!definition.params().isEmpty()
                    || !(definition.body() instanceof Hir.FnBody.Written written)
                    || !(evidence.declaredTypeOf(written.expr()) instanceof Type.Ref(TypeSymbol of))) {
                continue;
            }
            out.computeIfAbsent(of, _ -> new ArrayList<>()).add(entry.reachedAs());
        }
        return out;
    }
}
