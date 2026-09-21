package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
 *
 * <p>Which values are published is answered once, by {@link #publishedValues}. The entries, the
 * public methods of the class they are called through and the answers a module records for its
 * values are all that set and nothing wider, so the module's surface for a value is the same
 * whichever of them a reader looks at.
 */
public final class ValueEntries {

    private ValueEntries() {
    }

    /** The name the entry of {@code value} is emitted under. Written nowhere a source could spell. */
    public static String methodFor(String value) {
        return "$value." + value;
    }

    /**
     * The values {@code module} publishes: the definitions it wrote with no parameter list that
     * implement no behavior, and that it exposes.
     *
     * <p>What the module lists and no more, which is what another Souther module can import. A module
     * that lists nothing is public to Java and offers no name to import, so nothing of it is called
     * from another module. What a published helper names of this module's is not here either: a
     * helper is expanded into its reader, so nothing of the module's is called from outside on its
     * behalf.
     */
    public static Set<String> publishedValues(Hir.Module module) {
        Set<String> behaviors = new HashSet<>();
        for (Hir.BehaviorDef behavior : module.behaviors()) {
            behaviors.add(behavior.name());
        }
        Set<String> listed = new HashSet<>(module.exposing());
        Set<String> published = new LinkedHashSet<>();
        for (Hir.FnDef fn : module.fns()) {
            if (fn.params().isEmpty() && fn.body() != null
                    && fn.role() instanceof DefinitionRole.Ordinary
                    && !behaviors.contains(fn.name())
                    && listed.contains(fn.name())) {
                published.add(fn.name());
            }
        }
        return published;
    }

    /** The entry of every value {@code surface}'s module publishes, by the name each is emitted
     *  under. */
    public static Map<String, Hir.FnDef> emitted(CheckSurface surface, DeclarationNewtypes newtypes) {
        Hir.Module module = surface.module();
        Set<String> published = publishedValues(module);
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        for (Hir.FnDef value : module.fns()) {
            if (!published.contains(value.name())) {
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
}
