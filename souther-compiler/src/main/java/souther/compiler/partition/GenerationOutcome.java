package souther.compiler.partition;

import java.util.List;

/**
 * What the generator can do about one finding.
 *
 * <p>Every finding has one of these, and a finding with none is one an author is told nothing about
 * while the block above it reads as though it filled everything.
 *
 * <p><b>Asked of every finding and not of the ones a build refuses over.</b> What a bar refuses is
 * one question and what a search can compose a row for is another, and the first used to decide
 * which findings the second was asked about — so a finding some bar would refuse over and no bar
 * had been asked for went unanswered, and a strategy could only ever be written for what the bars
 * already gated on. The two are projections of one set of findings now, neither through the other.
 *
 * <p>Which of the four it is, is a question about strategies and not about searches. A strategy
 * that takes a finding of this kind and composed nothing is {@link CannotGenerate}; a finding no
 * strategy takes and one a strategy could be written for is {@link NotSupported}; a finding row
 * synthesis is not the answer to at all is {@link NotApplicable}. Whether anything was tried
 * belongs in the reason. Reading the kind off a search — nothing enumerated, so nothing supported —
 * would settle what the generator is able to do from what one run happened to touch, and the answer
 * would move with the model rather than with the compiler.
 *
 * <p>So a finding moves between the first three as strategies are written, and a strategy that
 * gains a form it can read moves findings from {@link NotSupported} to one of the others.
 * {@link NotApplicable} is not on that path: nothing anyone writes turns a measure this compiler
 * could not make into a row somebody can write.
 */
public sealed interface GenerationOutcome {

    /** A strategy applies, and it composed rows. */
    record Generated(List<Generator.GeneratedRow> candidates) implements GenerationOutcome {

        public Generated {
            candidates = List.copyOf(candidates);
        }
    }

    /**
     * A strategy applies, and it composed nothing.
     *
     * <p>And nothing more than that. Whether a row can be written at all is what the reasons carried
     * here answer — some of them say the model leaves no value there and a reader may act on it,
     * most of them say this compiler fell short and a reader may not — so the attempt is carried
     * whole and this arm claims neither. Read as always meaning the second, a run that had settled
     * the question would be printed under a sentence taking it back.
     *
     * <p><b>All of what was tried, and not the weakest of it.</b> An arm is looked for at every
     * combination claiming it, and those come to different things — one the model refuses, one the
     * search stopped at, one whose candidates were all rejected. Only the first of those says
     * anything about the arm itself, and none of the others orders against the rest: picking one to
     * carry meant picking by the order the search happened to walk, so the answer moved when the
     * cells were reordered and nothing about the model had changed.
     */
    record CannotGenerate(List<Generator.UnresolvedCombination> why) implements GenerationOutcome {

        public CannotGenerate {
            why = List.copyOf(why);
            if (why.isEmpty()) {
                throw new IllegalArgumentException("nothing came of something that was tried");
            }
        }

        /** One attempt, which is what a search asked about one thing at one place comes to. */
        public CannotGenerate(Generator.UnresolvedCombination why) {
            this(List.of(why));
        }
    }

    /**
     * Nothing here answers a finding row synthesis is not about.
     *
     * <p>Told apart from {@link NotSupported} because they are different pieces of news and only
     * one of them is a promise. That one says a strategy could be written and none has been; this
     * says there is nothing for a strategy to do — what a measure could not read is this compiler
     * falling short, and a position the model draws no line through is a fact about the model.
     * Written as one, a reader could not tell a row nobody has got round to composing from a
     * finding no row would answer, and every measurement shortfall would read as generator work
     * waiting to be done.
     */
    record NotApplicable(Reason reason) implements GenerationOutcome {

        /** Why row synthesis is not what answers it — a fact about the finding, not about a run. */
        public enum Reason {

            /** The measure could not be made, so what it did not find is not a set of gaps. */
            NOTHING_WAS_MEASURED(
                    "this is a measure this compiler could not make, and a row would answer a"
                            + " question that was never asked"),

            /** The model was read to the end and says this, which is not a shortfall in the rows. */
            A_FACT_ABOUT_THE_MODEL(
                    "this is what the model says rather than what its rows do not cover, and no row"
                            + " changes it"),

            /** What the rows were seen doing, which is an account and not an obligation. */
            AN_ACCOUNT_OF_WHAT_THE_ROWS_DID(
                    "this is what the rows were observed doing rather than something owed, so"
                            + " there is nothing here to compose a row for");

            private final String said;

            Reason(String said) {
                this.said = said;
            }

            /** The reason as a report writes it. */
            public String said() {
                return said;
            }
        }
    }

    /** No strategy takes a finding of this kind, or the form this one would need. */
    record NotSupported(Reason reason) implements GenerationOutcome {

        /**
         * Why nothing takes it — a fact about which strategies are written, not about the model.
         *
         * <p>Each of these is a strategy that could exist and does not. None of them says the gap
         * cannot be met, and none is read as evidence about the model.
         *
         * <p><b>Which the words have to carry too.</b> A sentence saying nothing composes an input
         * for an arm is read as there being no input that reaches it, and an author who writes the
         * row by hand has been told something false (issue #643). So each of these says what is
         * missing here, and what a reader does about it is write the row that this cannot.
         *
         * <p>Including where what is missing is upstream of the strategies. No axis at a position
         * is no classes <em>derived</em> there, and the position may well have cases — a sum this
         * could not read the rules of has its cases in the declaration and in no partition. Said as
         * there being no classes, it is the model that reads as having none.
         */
        public enum Reason {

            /**
             * The line is owed once across every reading of it, and the search is asked of one.
             *
             * <p>A row at the line is composed by walking one behavior's inputs, and a line an
             * {@code invariant} drew is owed by the declaration rather than by any of the behaviors
             * carrying the type (issue #1062). Which reading composes the one row a debt is owed is
             * a search over the readings and not a fold of them, and nothing does it yet.
             */
            NO_SEARCH_IS_ASKED_FOR_A_LINE_ACROSS_ITS_READINGS(
                    "a row is composed by walking one behavior's inputs, and this line is owed once"
                            + " over every behavior carrying the type"),

            /** The fork this arm belongs to is one no position of the inputs could be named for. */
            NO_WAY_INTO_THIS_ARM_CAN_BE_NAMED(
                    "a row is steered into an arm by the decisions that hold on the way there, and"
                            + " the fork this arm is of is one nothing could name a position for"),

            /** The ways to the value that leads to this arm could not all be written down. */
            THE_WAYS_INTO_THIS_ARM_ARE_NOT_ENUMERABLE(
                    "a row is steered into an arm by the decisions that hold on the way there, and"
                            + " the ways to this one could not all be written down — some of them"
                            + " would say a row arrives where it may not"),

            /** More ways into this arm than the reading of the body holds at once. */
            MORE_WAYS_IN_THAN_THE_READING_HOLDS(
                    "the ways into this arm run past what one reading of the body holds at once, so"
                            + " the reading stopped short of it rather than saying what steers a row"
                            + " there"),

            /** The arm stands in a function value, whose body runs where something calls it. */
            THE_ARM_RUNS_WHERE_SOMETHING_CALLS_IT(
                    "this arm is inside a block, which runs under whatever the thing that applies it"
                            + " is applied to — and that is not a class of this behavior's inputs"),

            /** Which arm of an attempted construction is taken is whether the value's rules held. */
            A_CONSTRUCTION_DECIDES_THIS_ARM(
                    "which arm of an attempted construction is taken is whether making the value"
                            + " held its own rules, and no class of an input names that"),


            /** Nothing searches for an input by the output it produces. */
            NO_STRATEGY_FOR_AN_OUTPUT_CASE(
                    "rows here are composed from what the input positions divide into, and nothing"
                            + " searches for one by the case it would answer with"),

            /** The position the case belongs to is not one any axis was derived at. */
            NO_AXIS_AT_THIS_POSITION("no axis was derived at the position this case belongs to, so"
                    + " no classes were derived there to compose a row from");

            private final String said;

            Reason(String said) {
                this.said = said;
            }

            /** The reason as a report writes it. */
            public String said() {
                return said;
            }
        }
    }
}
