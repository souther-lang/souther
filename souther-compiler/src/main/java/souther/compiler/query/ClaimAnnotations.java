package souther.compiler.query;

import souther.compiler.claims.ClaimVerdict;
import souther.compiler.claims.Claims;
import souther.compiler.inputs.Unsettlement;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a behavior's body declared cannot arrive, in the words a report writes.
 *
 * <p>Beside a measure and never inside one. What a row is owed at is counted with none of this in
 * scope ({@link Coverages}), and the two meet where a report is written — so a claim cannot narrow a
 * denominator by being in reach of the code that counts one, and what holds that is the shape of the
 * values rather than a rule somebody keeps. A decoration that took the measure and handed back
 * another was the same rule again: it could rebuild every number it was given.
 *
 * <p><b>One entry per case of a position, however many arms declared it.</b> A body may say the same
 * thing twice — two {@code match}es on one position, each with an arm for the case — and what left
 * the denominator is still one case. Counted per arm, a report said {@code excluded 2} of a position
 * with one case out of it. The reasons of every arm that said so are kept, in the order they were
 * written, because each of them is something the author wrote about that case.
 */
public record ClaimAnnotations(List<Said> all) {

    /** Nothing claimed, which is what most bodies come to. */
    public static final ClaimAnnotations NONE = new ClaimAnnotations(List.of());

    public ClaimAnnotations {
        all = List.copyOf(all);
    }

    /**
     * One case of one position, and what the model's own rules said about the claim.
     *
     * @param at      the position, spelled the way a rule about it is
     * @param why     what stopped the answer, or null where the rules refused the case and the claim
     *                says what they say
     * @param reasons what every arm declaring it wrote, in the order they were written
     */
    public record Said(String at, String classId, List<String> reasons, Why why) {

        public Said {
            reasons = List.copyOf(reasons);
        }

        /** Whether the rules bore the claim out, which is what tells a case out of the denominator
         *  from one still counted. */
        public boolean settled() {
            return why == null;
        }
    }

    /**
     * Why nothing settled a claim, in the words a report writes.
     *
     * <p>Deliberately coarser than what this compiler knows, and its own vocabulary rather than the
     * one an undivided position uses: what a reader is being told is what kind of thing stopped the
     * answer, and the two questions are not the same question.
     */
    public enum Why {

        /** A rule about the position was written and this compiler could not take it in. */
        A_RULE_WENT_UNREAD,

        /** The rules leave the position no value at all, which this compiler does not yet act on
         *  (issue #780), so every case of it is counted and none of them is settled. */
        THE_RULES_LEAVE_THE_POSITION_NOTHING,

        /** Nothing was read about the case: the position is past where the walk goes, or the claim
         *  names one the reading of the position does not have. */
        NOTHING_WAS_READ_ABOUT_THE_CASE,

        /** The rules leave the case standing, and the arm is inside another whose own condition
         *  nothing here reads. */
        THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED
    }

    /**
     * What {@code claims} came to, one entry per case of a position.
     *
     * <p>A claim the rules contradict is not here: it is refused where the body is checked, so a
     * report of that model is a report of one that did not compile.
     */
    public static ClaimAnnotations of(Claims claims) {
        if (claims.isEmpty()) {
            return NONE;
        }
        Map<String, Said> byCase = new LinkedHashMap<>();
        for (Claims.Judged judged : claims.all()) {
            if (judged.verdict() instanceof ClaimVerdict.Contradicted) {
                continue;
            }
            Why why = judged.verdict() instanceof ClaimVerdict.Unproven unproven
                    ? new UnsettledWords().of(unproven.why()) : null;
            String at = judged.claim().at().toString();
            String named = judged.claim().named().name();
            byCase.merge(at + " " + named,
                    new Said(at, named, judged.claim().reasons(), why),
                    ClaimAnnotations::and);
        }
        return new ClaimAnnotations(List.copyOf(byCase.values()));
    }

    /**
     * Two arms declaring one case, as one thing said about it.
     *
     * <p>The verdict is the position's answer about the case, so two arms about one case cannot
     * disagree about it; what each can have is words of its own, and both are kept.
     */
    private static Said and(Said had, Said also) {
        List<String> reasons = new ArrayList<>(had.reasons());
        also.reasons().stream().filter(each -> !reasons.contains(each)).forEach(reasons::add);
        return new Said(had.at(), had.classId(), reasons, had.why());
    }

    /** What a reader is told about a claim nothing settled. One projection, so that a distinction
     *  this compiler learns to make later is a word the report chooses to add rather than one it
     *  gains by accident. */
    /**
     * The one place a reason is turned into a word.
     *
     * <p>Named rather than written where it is used, so that what may ask a reason what it says is
     * one class and can be held to being one: the check that fixes this reads the compiled calls,
     * and a class with a name is what it can name.
     *
     * <p>One projection, so that a distinction this compiler learns to make later is a word the
     * report chooses to add rather than one it gains by accident — and it says a word for every arm
     * or does not compile.
     */
    private record UnsettledWords() implements souther.compiler.reach.WhyUnsettled.Words<Why> {

        /** What {@code why} says, in these words. */
        Why of(souther.compiler.reach.WhyUnsettled why) {
            return why.said(this);
        }

        @Override
        public Why noWitness() {
            return Why.THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED;
        }

        @Override
        public Why aConditionWasNotRead(souther.compiler.diag.SourcePos at) {
            return Why.A_RULE_WENT_UNREAD;
        }

        @Override
        public Why thePositionDidNotSettleIt(Unsettlement position) {
            // What the position said about its own cases, in the words it said it in.
            return said(position);
        }

        @Override
        public Why theWalkDidNotReachIt() {
            return Why.THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED;
        }
    }

    /** The same, for what a position answers about a case standing at it. */
    private static Why said(Unsettlement why) {
        return switch (why) {
            case Unsettlement.ReadingStopped _ -> Why.A_RULE_WENT_UNREAD;
            case Unsettlement.RulesLeaveNothing _ -> Why.THE_RULES_LEAVE_THE_POSITION_NOTHING;
            case Unsettlement.NoSuchDistinction _ -> Why.NOTHING_WAS_READ_ABOUT_THE_CASE;
        };
    }

    /** What was said about the position at {@code path}, in the order the body says it. */
    public List<Said> at(String path) {
        return all.stream().filter(each -> each.at().equals(path)).toList();
    }

    /** And what was said about every position not among {@code paths} — the ones no axis speaks
     *  for, which a report names by their position since there is no axis above them to. */
    public List<Said> notAt(List<String> paths) {
        return all.stream().filter(each -> !paths.contains(each.at())).toList();
    }
}
