package souther.compiler.observe;

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
    READINGS_OF_A_ROW_AT_A_POINT("how many readings of one row a point is tried against"),

    /** How many occurrences a walk of a container writes out, at every level it passes. */
    ELEMENTS_A_WALK_WRITES_OUT(
            "how many occurrences a walk of a container writes out, counted at every level"),

    /** How many fields down the rules about a value are followed. */
    FIELDS_A_RULE_IS_FOLLOWED_DOWN("how many fields down the rules about a value are followed"),

    /** How many combinations of two positions' classes are counted. */
    PAIRS_OF_CLASSES_COUNTED("how many combinations of two positions' classes are counted"),

    /** How many combinations in one group of decisions are measured. */
    COMBINATIONS_OF_A_GROUP_MEASURED(
            "how many combinations in one group of decisions are measured"),

    /** How many runs replacing an arm may be made. */
    RUNS_REPLACING_AN_ARM("how many runs replacing an arm may be made"),

    /** How much of a sibling arm a fork carries for a run replacing an arm. */
    NODES_A_FORK_CARRIES("how much of the arm beside it a fork carries for a run replacing it"),

    /** How much code one method may hold, which is the JVM's figure and not this compiler's. */
    CODE_ONE_METHOD_HOLDS("how much code one method of the JVM holds"),

    /** States one machine for the values a position admits may have. */
    ADMITTED_VALUES_ONE_MACHINE(
            "how many states one machine for the values a position admits may have"),

    /** What building the machines for the values a position admits may make and look at. */
    ADMITTED_VALUES_IN_ALL(
            "how much building the machines for the values a position admits may make and look at"),

    /** States one machine for where the strings a rule admits stop may have. */
    ORDERED_EXTENT_ONE_MACHINE(
            "how many states one machine for where the strings a rule admits stop may have"),

    /** What building the machines for where the strings a rule admits stop may make and look at. */
    ORDERED_EXTENT_IN_ALL("how much building the machines for where the strings a rule admits"
            + " stop may make and look at"),

    /** States one machine for the strings a behavior tells apart may have. */
    BEHAVIOR_DISTINCTIONS_ONE_MACHINE(
            "how many states one machine for the strings a behavior tells apart may have"),

    /** What building the machines for the strings a behavior tells apart may make and look at. */
    BEHAVIOR_DISTINCTIONS_IN_ALL("how much building the machines for the strings a behavior tells"
            + " apart may make and look at"),

    /** States one machine for the set one rule of a position admits may have. */
    RULE_SETS_ONE_MACHINE(
            "how many states one machine for the set one rule of a position admits may have"),

    /** What building the machines for the sets each rule of a position admits may make and look
     *  at. */
    RULE_SETS_IN_ALL("how much building the machines for the sets each rule of a position admits"
            + " may make and look at"),

    /** How many steps the run of one row may take. */
    EVALUATION_STEPS("how many steps the run of one row may take"),

    /** How deep the run of one row may call. */
    RECURSION_DEPTH("how deep the run of one row may call"),

    /** How long compiling what one row runs may take. */
    COMPILER_TIME("how long compiling what one row runs may take"),

    /** How deep a value a run produced is kept. */
    OBSERVED_DEPTH("how deep a value a run produced is kept"),

    /** How many parts of a value a run produced are kept. */
    OBSERVED_NODES("how many parts of a value a run produced are kept"),

    /** How many elements of a container a run produced are kept. */
    OBSERVED_ELEMENTS("how many elements of a container a run produced are kept"),

    /** How many characters of a string a run produced are kept. */
    OBSERVED_TEXT("how many characters of a string a run produced are kept");

    private final String counts;

    WorkFigure(String counts) {
        this.counts = counts;
    }

    /** What it counts, in the words a report says it in. */
    public String counts() {
        return counts;
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
        public String counts() {
            return figure.counts();
        }
    }
}
