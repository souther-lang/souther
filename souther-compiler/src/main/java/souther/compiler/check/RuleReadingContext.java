package souther.compiler.check;

import souther.compiler.numeric.Today;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.types.TypeKey;
import souther.compiler.values.StringFacts;
import souther.compiler.values.StringMachineAnswers;

/**
 * The one world a reading of a declaration's rules is made in: where the rules are read from, what
 * the reading may spend, and where it borrows what somebody has already made of the same
 * declaration.
 *
 * <p><b>Not a joining of what is read with what may be spent.</b> {@link RuleReadingSource} says
 * why those two are separate arguments, and they still are: neither is part of the other, and this
 * holds both without either answering for the other. What is stated here is about a walk rather
 * than about a rule — that the three travel together down a walk that comes back to itself, and
 * that a step of it substituting one of them is a step reading some other world.
 *
 * <p>Which is a fact about what a reading costs rather than about what it answers. A walk that
 * proposes a value for a position reaches the position's element, which is the same question again,
 * and each turn of it asks what the rules of some declaration leave. Handed the lender, every turn
 * borrows the declaration's canonical reading; handed {@link DeclarationReadings#NONE} at one turn,
 * that turn reads the declaration whole again — which is the same answer at a cost the measured
 * difference is orders of magnitude of. So a call that keeps the answer and drops the lender is
 * correct and is not the same call, and nothing in a signature taking the three apart says so.
 *
 * <p>What travels down a walk and not what a result of it keeps. A result that outlives the walk
 * keeps what it needs of this ({@link #retainedReadings}) and not the context: held in a result,
 * the rules and the budget would be carried into what somebody else compares.
 *
 * <p>And the day a value it proposes is chosen near ({@link #today}), which travels with the
 * three because every reader that proposes a value is handed this and nothing else.
 *
 * <p>What it was made of and nothing else: the rules, the budget, and the lender — once for a
 * reader under the walk that uses it and once for a result that keeps it past the walk. A context
 * that answered questions of its own — what a name
 * resolves to, what a declaration's fields leave — would be where a reader goes instead of where a
 * reader gets what it was given, and every such answer is one somebody already owns.
 *
 * <p>And one world derived from another ({@link #whileTheAnswerIsMade}), which is not an answer of
 * that kind: what comes back is the same three under a bound on one of them. It is here because a
 * bound put on the lender alone holds only while the world around it is put back together by hand,
 * and a walk handed the lender can reach past a bound nobody rebuilt.
 *
 * <p>No identity of its own, which is why this is not a record. Two of the three are capabilities,
 * so two contexts built from one compilation for one reading answer alike and compare unlike, and
 * an equality generated here would be one a caller could take for "the same world" and find false.
 * A reader telling two readings apart asks {@link RuleReadingSource.Origin}.
 */
public final class RuleReadingContext {

    private final RuleReadingSource source;
    private final ReadingPolicy policy;
    private final DeclarationReadings readings;
    private final Today today;

    private RuleReadingContext(RuleReadingSource source, ReadingPolicy policy,
                               DeclarationReadings readings, Today today) {
        if (source == null || policy == null || readings == null || today == null) {
            throw new IllegalArgumentException("a reading is made of rules, under a budget, from"
                    + " what is lent to it, and on a day");
        }
        this.source = source;
        this.policy = policy;
        this.readings = readings;
        this.today = today;
    }

    /** The world a reader with a lender to hand reads in. */
    public static RuleReadingContext of(RuleReadingSource source, ReadingPolicy policy,
                                        DeclarationReadings readings, Today today) {
        return new RuleReadingContext(source, policy, readings, today);
    }

    /**
     * The same, for a reader that has nothing to borrow from and reads each declaration whole
     * however many times it arrives at one.
     *
     * <p>Named, because that is what it is. {@link DeclarationReadings#NONE} is not the absence of a
     * decision to be filled in by whichever overload was to hand — it is the reading done again
     * every time, and a caller inside a walk that reaches one declaration from several positions
     * pays for it once per arrival. So it is asked for here rather than supplied by an overload
     * that leaves the lender out.
     */
    public static RuleReadingContext unshared(RuleReadingSource source, ReadingPolicy policy,
                                              Today today) {
        return new RuleReadingContext(source, policy, DeclarationReadings.NONE, today);
    }

    /** Where the rules are read from. */
    public RuleReadingSource source() {
        return source;
    }

    /** What the reading may spend. */
    public ReadingPolicy policy() {
        return policy;
    }

    /**
     * The day a value chosen in this world is chosen near, where nothing the rules say fixes it.
     *
     * <p>Every value a reading proposes — the one a measurement shows a class holds, and the one a
     * row is written with — is chosen on this day, so a row offers the value its class was shown to
     * hold. Which values the rules leave is not read off it.
     */
    public Today today() {
        return today;
    }

    /**
     * Where it borrows what has already been made of a declaration.
     *
     * <p>For a reader that uses the lender itself — borrows a reading or its string machines from
     * it, or keeps where the revision found sets to stop — and not for handing it on to another step
     * under the walk. A step below is handed this context and reads in it; handed the lender apart,
     * it could put some other world together around it, and {@link #whileTheAnswerIsMade} is what a
     * reader that has to bound one uses instead.
     */
    DeclarationReadings readings() {
        return readings;
    }

    /**
     * What the revision this reading is made under has worked out
     * ({@link DeclarationReadings#revision}).
     *
     * <p>That one capability of the lender and not the lender: a reader outside this package that
     * offers values has no business borrowing readings, and handed the lender it could.
     */
    public RevisionKnowledge revision() {
        return readings.revision();
    }

    /**
     * What a result of the walk keeps for readers of the same declarations that start after the
     * walk is over.
     *
     * <p>Where this world ends and what outlives it begins. A step under the walk is handed this
     * context and not the lender taken out of it; a result the walk builds may keep the lender, so
     * that a reader arriving later borrows what the walk made rather than making it again. Named
     * for that and not for the lender, so that a caller taking it out to hand to a step below is
     * visibly doing something else.
     */
    public DeclarationReadings retainedReadings() {
        return readings;
    }

    /**
     * The same world, for the length of the answer about {@code named}'s machines that is being
     * made: the same rules, the same budget, and a lender bounded as
     * {@link DeclarationReadings#whileTheAnswerIsMade} bounds one.
     *
     * <p>Here rather than at the lender because what travels down a walk is this. A reader that
     * took the lender out, bounded it and put a world back together would be building a world of
     * its own, and the boundary would hold only for as long as every such reader remembered to
     * rebuild it — which is what a walk reaching the lender from underneath walks around. Derived
     * here, a reader below is handed a bounded world and has no other to hand on.
     */
    public RuleReadingContext whileTheAnswerIsMade(TypeKey named, StringMachineAnswers recorder) {
        return new RuleReadingContext(source, policy,
                readings.whileTheAnswerIsMade(named, recorder), today);
    }

    /**
     * The same rules and budget, for a counterfactual of a reading of {@code named} that came to
     * {@code machines}: borrowing those and nothing else, with what the revision has worked out
     * ({@link DeclarationReadings#borrowing}).
     *
     * <p>Here for the reason {@link #whileTheAnswerIsMade} is: a reader that took the lender out to
     * put a world of its own together would be past the bound a producer put on this one.
     */
    RuleReadingContext forACounterfactual(TypeKey named, StringFacts machines) {
        return new RuleReadingContext(source, policy,
                DeclarationReadings.borrowing(named, machines, readings.revision()), today);
    }
}
