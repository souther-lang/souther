package souther.compiler.observe;

import souther.compiler.diag.Messages;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.SearchMessage;

import java.util.Locale;
import java.util.Objects;

/**
 * The figures this compiler holds its work to outside the composing stage: what reading a model,
 * measuring it, running its rows and keeping what a run did may each come to.
 *
 * <p>Some are fixed where they are declared and some are handed to a run by a policy, so a member
 * says which figure and {@link At} carries what it stood at: two runs under two policies reach the
 * same member at two numbers, and a reader is owed the number the run it is reading used.
 *
 * <p>The machines that read a string's patterns are held to two limits at once — the states one
 * machine may have, and what everything built for one answer may make and look at between them —
 * so each purpose they are built for has a member for each.
 */
public enum WorkFigure {

    /** How many readings of one row a point is tried against. */
    READINGS_OF_A_ROW_AT_A_POINT(new SearchMessage.ReadingsOfARowAtAPoint()),

    /** How many occurrences a walk of a container writes out, at every level it passes. */
    ELEMENTS_A_WALK_WRITES_OUT(new SearchMessage.ElementsAWalkWritesOut()),

    /** How many fields down the rules about a value are followed. */
    FIELDS_A_RULE_IS_FOLLOWED_DOWN(new SearchMessage.FieldsARuleIsFollowedDown()),

    /** How many parts of the choices a path leaves undecided are taken alone along the path, to
     *  settle them over what it comes to know. */
    PARTS_A_PATH_SETTLES(new SearchMessage.PartsAPathSettles()),

    /** How many combinations of two positions' classes are counted. */
    PAIRS_OF_CLASSES_COUNTED(new SearchMessage.PairsOfClassesCounted()),

    /** How many combinations in one group of decisions are measured. */
    COMBINATIONS_OF_A_GROUP_MEASURED(new SearchMessage.CombinationsOfAGroupMeasured()),

    /** How many runs replacing an arm may be made. */
    RUNS_REPLACING_AN_ARM(new SearchMessage.RunsReplacingAnArm()),

    /** How much of a sibling arm a fork carries for a run replacing an arm. */
    NODES_A_FORK_CARRIES(new SearchMessage.NodesAForkCarries()),

    /** How many readings of a combination a search for a row at it tries. */
    READINGS_OF_A_COMBINATION_TRIED(new SearchMessage.ReadingsOfACombinationTried()),

    /** How many rows composed for one reading of a combination are run. */
    RUNS_FOR_ONE_READING(new SearchMessage.RunsForOneReading()),

    /** How many candidates a walk repairing a row builds. */
    CANDIDATES_A_REPAIR_BUILDS(new SearchMessage.CandidatesARepairBuilds()),

    /** How many assignments a walk repairing a row looks at, passed over or built. */
    ASSIGNMENTS_A_REPAIR_LOOKS_AT(new SearchMessage.AssignmentsARepairLooksAt()),

    /** States one machine for the values a position admits may have, and what making it may look
     *  at. */
    ADMITTED_VALUES_ONE_MACHINE(new SearchMessage.AdmittedValuesOneMachine()),

    /** What building the machines for the values a position admits may make and look at. */
    ADMITTED_VALUES_IN_ALL(new SearchMessage.AdmittedValuesInAll()),

    /** States one machine for where the strings a rule admits stop may have, and what making it
     *  may look at. */
    ORDERED_EXTENT_ONE_MACHINE(new SearchMessage.OrderedExtentOneMachine()),

    /** What building the machines for where the strings a rule admits stop may make and look at. */
    ORDERED_EXTENT_IN_ALL(new SearchMessage.OrderedExtentInAll()),

    /** States one machine for the strings a behavior tells apart may have, and what making it may
     *  look at. */
    BEHAVIOR_DISTINCTIONS_ONE_MACHINE(new SearchMessage.BehaviorDistinctionsOneMachine()),

    /** What building the machines for the strings a behavior tells apart may make and look at. */
    BEHAVIOR_DISTINCTIONS_IN_ALL(new SearchMessage.BehaviorDistinctionsInAll()),

    /** States one machine for the set one rule of a position admits may have, and what making it
     *  may look at. */
    RULE_SETS_ONE_MACHINE(new SearchMessage.RuleSetsOneMachine()),

    /** What building the machines for the sets each rule of a position admits may make and look
     *  at. */
    RULE_SETS_IN_ALL(new SearchMessage.RuleSetsInAll()),

    /** States one machine for the strings that part into pieces of a type may have, and what
     *  making it may look at. */
    STRINGS_PARTED_ONE_MACHINE(new SearchMessage.StringsPartedOneMachine()),

    /** What building the machines for the strings that part into pieces of a type may make and
     *  look at. */
    STRINGS_PARTED_IN_ALL(new SearchMessage.StringsPartedInAll()),

    /** How many steps the run of one row may take. */
    EVALUATION_STEPS(new SearchMessage.EvaluationSteps()),

    /** How deep the run of one row may call. */
    RECURSION_DEPTH(new SearchMessage.RecursionDepth()),

    /** How long compiling what one row runs may take. */
    COMPILER_TIME(new SearchMessage.CompilerTime()),

    /** How deep a value a run produced is kept. */
    OBSERVED_DEPTH(new SearchMessage.ObservedDepth()),

    /** How many parts of a value a run produced are kept. */
    OBSERVED_NODES(new SearchMessage.ObservedNodes()),

    /** How many elements of a container a run produced are kept. */
    OBSERVED_ELEMENTS(new SearchMessage.ObservedElements()),

    /** How many characters of a string a run produced are kept. */
    OBSERVED_TEXT(new SearchMessage.ObservedText());

    private final Message counted;

    WorkFigure(Message counted) {
        this.counted = counted;
    }

    /** What it counts, in whichever language a report is written. */
    public Message countsSaid() {
        return counted;
    }

    // BRIDGE-1464: callers move to countsSaid
    public String counts() {
        return Messages.render(counted, Locale.ENGLISH);
    }

    /** This figure, as it stood at {@code most}. */
    public Figure at(long most) {
        return new At(this, Long.toString(most));
    }

    /** This figure, as it stood at {@code most}, said in the words of what it counts. */
    public Figure at(String most) {
        return new At(this, most);
    }

    /** A member, and what it stood at on the run that reached it. */
    public record At(WorkFigure figure, String most) implements Figure {

        public At {
            Objects.requireNonNull(figure, "a figure reached is some figure");
            Objects.requireNonNull(most, "a figure reached stood at something");
        }

        @Override
        public String name() {
            return figure.name();
        }

        @Override
        public Message countsSaid() {
            return figure.countsSaid();
        }
    }
}
