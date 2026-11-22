package souther.compiler.query;

import souther.compiler.partition.AChoiceReadThrough;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ModelOccurrence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The conditions of one behavior whose values are made through more choices than this compiler
 * reads one condition on, and what to declare as behaviors so that they are not.
 *
 * <p><b>Asked of how the values are written, before anything is read of the conditions.</b> A
 * condition is read once on each arm of a choice its values are made through, and what decides
 * between the arms is read beside them, so the readings multiply with each choice
 * ({@link AChoiceReadThrough#readings}). What is counted here is the most they may come to: an arm
 * no run takes is not read, so a condition told of here may be read whole all the same. Which
 * conditions stopped is another question, answered of the reading
 * ({@link ConditionsStoppedAtAFigure}), and what is told here is what a reading may cost.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record ConditionsReadThroughTooManyChoices(String name, String behavior)
        implements Key<WhatToDeclare> {

    /** The readings of one condition past which it is told of. */
    public static int most() {
        return CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum();
    }

    /** What is told of one behavior of one module. */
    public record Said(String module, String behavior, WhatToDeclare told) {}

    /**
     * What is told of each behavior {@code compilation} measures, in the order they are declared,
     * leaving out those nothing is told of. Nothing the measurement makes is asked for it.
     */
    public static List<Said> toldOf(Compilation compilation) {
        List<Said> out = new ArrayList<>();
        WhatIsBeingMeasured.toBeMeasuredIn(compilation).forEach((module, behaviors) ->
                behaviors.forEach(behavior -> {
                    WhatToDeclare told = compilation.db()
                            .ask(new ConditionsReadThroughTooManyChoices(module, behavior))
                            .value();
                    if (told != null && told.conditions() > 0) {
                        out.add(new Said(module, behavior, told));
                    }
                }));
        return List.copyOf(out);
    }

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<WhatToDeclare> compute(Db db) {
        List<AComparisonRead> read = db.ask(new Adequacy.ComparisonsRead(name, behavior)).value();
        return read == null ? Answer.absent() : Answer.of(told(read));
    }

    /** What is told of {@code conditions}, each where the walk of the body met it. */
    static WhatToDeclare told(List<AComparisonRead> conditions) {
        Set<ModelOccurrence> past = new LinkedHashSet<>();
        for (AComparisonRead each : conditions) {
            if (WhatToDeclare.readings(each.through())
                    .compareTo(BigInteger.valueOf(most())) > 0) {
                past.add(each.copy());
            }
        }
        return past.isEmpty() ? WhatToDeclare.NOTHING : WhatToDeclare.of(past, conditions);
    }
}
