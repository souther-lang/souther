package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The definitions a module emits so that a value it publishes can be read from another module
 * without that module holding a copy of it.
 *
 * <p>One per published value, taking nothing and answering with the value. Its body is a reference
 * to the value and nothing else, so it goes through every pass a body goes through and the region
 * that reads the reference is the one that decides what the value needs and builds it once. The
 * dependencies of a value are not worked out here, which is what keeps a second account of them
 * from existing.
 *
 * <p>Minted like a row's operand and for the same reason: nothing inlines it, because nothing in
 * this module calls it. Unlike a row's it is shipped, since what calls it is another module.
 */
public final class ValueEntries {

    private ValueEntries() {
    }

    /** The name the entry of {@code value} is emitted under. Written nowhere a source could spell. */
    public static String methodFor(String value) {
        return "$value." + value;
    }

    /**
     * The entry of every value {@code surface}'s module exposes, by the name each is emitted under.
     *
     * <p>A value is a definition with no parameters that is not a behavior's implementation and that
     * the module wrote itself. What is exposed is what the module lists, which is the surface
     * another module imports from.
     */
    public static Map<String, Hir.FnDef> emitted(CheckSurface surface, DeclarationNewtypes newtypes) {
        Hir.Module module = surface.module();
        Set<String> behaviors = new HashSet<>();
        for (Hir.BehaviorDef behavior : module.behaviors()) {
            behaviors.add(behavior.name());
        }
        Map<String, Hir.FnDef> declared = new LinkedHashMap<>();
        for (Hir.FnDef fn : module.fns()) {
            if (fn.body() != null && fn.role() instanceof DefinitionRole.Ordinary
                    && !behaviors.contains(fn.name())) {
                declared.put(fn.name(), fn);
            }
        }
        // Worked out once for the module and not once for each value asked about.
        Set<String> reachable = reachableFromOutside(module, declared);
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        for (Hir.FnDef value : declared.values()) {
            if (!value.params().isEmpty() || !reachable.contains(value.name())) {
                continue;
            }
            String name = methodFor(value.name());
            Hir.Var reference = Hir.Var.respelled(value.name(),
                    new ReachName.Own(new ValueName.Helper(module.name(), value.name())),
                    new FixtureReferenceOrigin(0), value.pos(), null);
            Hir.FnDef entry = new Hir.FnDef(WrittenName.synthetic(name, value.pos()), module.name(),
                    List.of(), null, new Hir.FnBody.Written(reference),
                    new Hir.Modifiers(true, true),
                    new DefinitionRole.RowValue(new RowPosition.Supplies(null)), value.pos());
            out.put(name, Desugared.Fn.desugar(entry, newtypes).read());
        }
        return out;
    }

    /**
     * The names another module calls the entry of: what is exposed, and what a helper that is exposed
     * names, directly or through the helpers that one names in turn.
     *
     * <p>A published helper is expanded into the module that calls it, and what it names of this
     * module's is named there. So a value that only a published definition reaches is read from
     * outside exactly as an exposed one is, and needs the same entry.
     */
    private static Set<String> reachableFromOutside(Hir.Module module,
                                                    Map<String, Hir.FnDef> declared) {
        Set<String> seen = new HashSet<>();
        ArrayDeque<String> work = new ArrayDeque<>();
        for (String exposed : module.exposing()) {
            if (declared.containsKey(exposed) && seen.add(exposed)) {
                work.add(exposed);
            }
        }
        while (!work.isEmpty()) {
            String next = work.poll();
            // A value runs where it is declared, so what it names is built there and needs no
            // entry. Only a helper is expanded into the reader, and only what it names is named
            // there.
            if (declared.get(next).params().isEmpty()) {
                continue;
            }
            for (ValueName.Helper reached : HelperNames.helpersReached(declared.get(next).writtenBody())) {
                if (reached.module().equals(module.name()) && declared.containsKey(reached.name())
                        && seen.add(reached.name())) {
                    work.add(reached.name());
                }
            }
        }
        return seen;
    }
}
