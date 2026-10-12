package souther.compiler.core;

import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * A copy of one of the language's operations, made where an application of it is written, and the
 * application it was made for.
 *
 * <p>An operation the library writes in the language is copied into a body where it is applied,
 * and nothing in either tree is the application itself. Which copy a node's code belongs to is what
 * the node's lineage says, and the application is the call the copy was made at. Both the place a
 * run's answer is recorded at and a rule read off that answer are about the application, so both
 * find it here, from where the copy came from and not from the shape its code happens to take.
 *
 * @param copy        the copy, as the lineage of the code it holds says
 * @param application the application, as it is written where the copy was made
 */
public record ACopyOfAnApplication(OccurrenceLineage.Expansion copy,
                                   ConstructOccurrence application) {

    public ACopyOfAnApplication {
        Objects.requireNonNull(copy, "a copy is some copy");
        Objects.requireNonNull(application, "of an application written somewhere");
    }

    /**
     * The copy {@code e}'s code belongs to, where it is the copy of one of the language's
     * operations made at an application — or null where {@code e} says nothing of where it is, or
     * is code no such copy holds.
     *
     * <p>The nearest copy and no other. Code written inside another operation's own body is copied
     * once for each application of that operation, and belongs to the copy it was made in.
     */
    public static ACopyOfAnApplication of(Core e) {
        ConstructOccurrence occurrence = occurrenceOf(e);
        if (occurrence == null || !occurrence.isWritten()
                || !(occurrence.lineage() instanceof OccurrenceLineage.Expansion copy)
                || !(copy.expanded() instanceof ValueName.Stdlib.Operation)
                || !(copy.at() instanceof ExpansionSite.Written written)) {
            return null;
        }
        return new ACopyOfAnApplication(copy,
                new ConstructOccurrence(written.origin(), copy.within()));
    }

    /**
     * Where {@code e} is written, for a node that carries it, or null for one that does not: a
     * name, a literal, a binding, and a value built from parts stand wherever their parent does.
     *
     * <p>Asked of the node a walk stands at, and not of what it holds. A widening is a node of its
     * own, standing as another type, and says nothing of where it is; the node it holds is asked
     * next, when the walk gets to it.
     */
    public static ConstructOccurrence occurrenceOf(Core e) {
        return switch (e) {
            case Core.Widen _ -> null;
            case Core.Binary binary -> binary.occurrence();
            case Core.Call call -> call.occurrence();
            case Core.If iff -> iff.occurrence();
            case Core.IfConstructed attempt -> attempt.occurrence();
            case Core.Match match -> match.occurrence();
            default -> null;
        };
    }

    /** Whether {@code let} binds something of a copy of one of the language's operations. */
    public static boolean ofACopyOfAnOperation(Core.LetIn let) {
        return let.binder().binding().owner() instanceof BindingOwner.Expansion copy
                && copy.expanded() instanceof ValueName.Stdlib.Operation;
    }
}
