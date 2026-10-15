package souther.compiler.meaning;

import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * A choice the author of a comparison wrote, as the comparison's own definition has it: which
 * construct, and through which calls that definition makes.
 *
 * <p>A comparison in a helper is read once per call, and each copy reaches values two ways. What the
 * definition computes from its parameters — an {@code if} in an operand, the cases of an operation
 * it applies, the body of a helper it calls — is the same in every copy, and a choice there divides
 * what the author wrote into lines. What a parameter is given is the caller's, different in each
 * copy, and a choice there divides one line into the places a call put it. Only the first is one of
 * these.
 *
 * <p>Told apart by the copy each construct stands in. The comparison's copy, or a copy made by a
 * call written inside it, is the definition's; any other is something a caller handed in. A copy
 * made by applying a function the definition was given is the caller's too, whatever body it is of:
 * the function is a value of the call.
 *
 * @param origin the construct as the source wrote it
 * @param within the calls between the comparison's definition and the construct, outermost first;
 *               empty where the definition wrote the construct itself
 */
public record WrittenChoice(SourceConstructOrigin origin, List<ExpansionLineage.Step> within) {

    public WrittenChoice {
        Objects.requireNonNull(origin, "a choice is some construct");
        within = List.copyOf(within);
    }

    /**
     * The choice {@code construct} is, where the definition of a comparison standing in
     * {@code comparison} wrote it — or nothing, where a caller handed it in.
     */
    public static Optional<WrittenChoice> of(ConstructOccurrence construct,
                                             ExpansionLineage comparison) {
        if (!construct.isWritten()) {
            return Optional.empty();
        }
        List<ExpansionLineage.Step> between = new ArrayList<>();
        ExpansionLineage at = construct.lineage().expansionProjection();
        while (!at.equals(comparison)) {
            if (!(at instanceof ExpansionLineage.Expansion copy)
                    || copy.expanded() instanceof ValueName.Local
                    || copy.at() instanceof ExpansionSite.Supplied) {
                return Optional.empty();
            }
            between.add(copy.step());
            at = copy.within();
        }
        Collections.reverse(between);
        return Optional.of(new WrittenChoice(construct.origin(), between));
    }
}
