package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.InputReads;
import souther.compiler.sites.WrittenCondition;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The conditions one reading of a body met, and the name each of them goes by.
 *
 * <p><b>A register of what was met and not a count of the reading.</b> A subtree is read as a
 * condition more than once — the walk reads a short-circuit operator's left operand to say what
 * stands past it, and reads it again inside whatever encloses it — and every one of those readings
 * is of the same condition. Counted per reading, one condition would wear as many names as the
 * shape of the tree happens to produce, and a reader joining two accounts on the name would join
 * them on nothing.
 *
 * <p>So a name and what it names are one act: the first reading of a site asks for the next name,
 * and every reading after it is answered with what the first came to. A number paired with a
 * condition anywhere else would be that correspondence built a second time, by something that had
 * not done the recognising.
 *
 * <p><b>One of these per body read, and every condition of that reading takes its name here.</b> A
 * condition of a guard and an arm of a fork are both things a row had to satisfy to get somewhere,
 * so they are counted together: numbered apart, two of them would wear one name and nothing
 * downstream could tell them apart.
 *
 * <p>It also says which question places a condition, because that is settled where the condition is
 * read and nowhere else. Whether the code is written somewhere a reader can open is what a position
 * already says, and it is the one thing about a position that survives the code moving — so it is
 * the last thing read off the position, and what comes out is which question a report puts later.
 *
 * <p>Where the answer is this reading's own, the place is written down in the same act. So there is
 * one entry per condition a report can ask about and none for the ones whose construct a reader can
 * go and open.
 */
final class ConditionNumbering {

    /**
     * One condition of this reading: the node a fold arrives at, under the names in force there.
     *
     * <p><b>The two halves are compared differently, and each for its own reason.</b> A site is
     * which node the reading arrived at, which is an identity question: a node is the same site as
     * itself and as nothing else, and asking a whole subtree whether it says what another says
     * would make what it costs to name a condition grow with the tree the condition is in. Today
     * either comparison would tell the nodes apart — a {@link Core} node carries where it stands —
     * so what is settled here is which question a site is, not which nodes happen to be told apart.
     *
     * <p>The names in force are what they say and not which object says them: a {@code let} body
     * reached by two folds is under two environments built the same way, and read as two sites the
     * condition inside it would be named twice.
     *
     * <p>The node the fold arrives at, which is not the node it was handed. Bindings and a name
     * standing for a truth are looked through on the way in, so a condition reached through one is
     * the same condition as the one reached without.
     */
    private record Site(Core node, InputReads reads) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Site that && node == that.node && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(node) * 31 + reads.hashCode();
        }
    }

    private final String module;
    private final String behavior;
    /** Which reading of the body this is, which the names it hands out say beside their number. */
    private final ConditionOccurrence.Reading reading;
    private final Map<Site, Condition> read = new HashMap<>();
    /** The name each arm of each fork goes by. Beside {@link #read} because an arm is not a fold of
     *  a subtree: what is met is the fork and which of its arms, and there is no node of its own to
     *  be at. A {@code match} and an attempt both, since an arm of either is met the same way. */
    private final Map<Core, Map<Integer, ConditionOccurrence>> arms = new IdentityHashMap<>();
    private final Map<ConditionOccurrence, Citation> metAt;
    /** Which construct of the model, in which copy of it, each condition named here is. Shared with
     *  every place this reading reads, as the names are. */
    private final Map<ConditionOccurrence, ModelOccurrence> stands;
    /** The copy that made each entry this reading put on a way, by the entry itself, shared with
     *  every place this reading reads. Two equal entries are two entries here, each made by its
     *  own copy. */
    private final Map<OnTheWay, ModelOccurrence> madeBy;
    /** How many names this reading has handed out, shared with every place it reads. */
    private final int[] next;
    /** What this reading names inside the body of each call of a recursive helper it reads, by the
     *  call, shared with every place it reads. */
    private final Map<CallContext, ConditionNumbering> within;

    ConditionNumbering(String module, String behavior, ConditionOccurrence.Reading reading) {
        this(module, behavior, reading, new LinkedHashMap<>(), new LinkedHashMap<>(),
                new IdentityHashMap<>(), new int[1], new HashMap<>());
    }

    private ConditionNumbering(String module, String behavior, ConditionOccurrence.Reading reading,
                               Map<ConditionOccurrence, Citation> metAt,
                               Map<ConditionOccurrence, ModelOccurrence> stands,
                               Map<OnTheWay, ModelOccurrence> madeBy, int[] next,
                               Map<CallContext, ConditionNumbering> within) {
        this.module = module;
        this.behavior = behavior;
        this.reading = reading;
        this.metAt = metAt;
        this.stands = stands;
        this.madeBy = madeBy;
        this.next = next;
        this.within = within;
    }

    /**
     * The same reading, inside the body of a recursive helper read at the call {@code context}
     * names.
     *
     * <p>One body read at two calls is two places the reading has been, and a fork in it is met at
     * each: what one call's arms are named is not the other's. The names are this reading's and
     * counted with every other it hands out, so two calls never wear one name.
     */
    ConditionNumbering within(CallContext context) {
        return context.equals(CallContext.OF_THE_BODY) ? this
                : within.computeIfAbsent(context,
                        _ -> new ConditionNumbering(module, behavior, reading, metAt, stands,
                                madeBy, next, within));
    }

    /** What this reading already made of the condition at {@code at} under {@code reads}, or null
     *  where it has not met it. */
    Condition alreadyRead(Core at, InputReads reads) {
        return read.get(new Site(at, reads));
    }

    /** Files {@code condition} as what the condition at {@code at} under {@code reads} is. */
    void read(Core at, InputReads reads, Condition condition) {
        read.put(new Site(at, reads), condition);
    }

    /** The name of the condition being recognised now, where no construct of the model is it. */
    ConditionOccurrence met() {
        return new ConditionOccurrence(behavior, reading, next[0]++);
    }

    /**
     * The name of the condition being recognised now, it being {@code written}.
     *
     * <p>Which copy of the model's construct it is, is filed in the same act. A helper's condition
     * is one construct written once and met once per call, and the names already tell those apart;
     * what a reader is shown to tell them apart by is the call each copy was made at, and that is
     * the occurrence's to say. Paired with a name anywhere else, it would be this correspondence
     * made a second time by something that had not done the recognising.
     *
     * <p>Nothing is filed where the model states nothing at the construct — one the source never
     * wrote, or one inside the language's own operations ({@link ModelOccurrence#statedAt}).
     */
    ConditionOccurrence met(ConstructOccurrence written) {
        ConditionOccurrence met = met();
        if (written.isWritten()) {
            ModelOccurrence.statedAt(written).ifPresent(stated -> stands.put(met, stated));
        }
        return met;
    }

    /**
     * The name reaching {@code part} of {@code fork} goes by.
     *
     * <p>Refused where this reading has already named that arm, rather than answered with the name
     * it gave the first time. A fold of a subtree is asked for more than once and is registered
     * because of it; an arm is met where the walk meets the fork, and a second naming would be a
     * walk that had come to reach one arm twice — which is a walk saying a row satisfied one thing
     * two ways, and nothing downstream could tell the two apart. So it is raised here rather than
     * resolved by keeping one of them.
     */
    ConditionOccurrence metEntering(Core fork, ConstructOccurrence written, int part) {
        Map<Integer, ConditionOccurrence> named =
                arms.computeIfAbsent(fork, _ -> new LinkedHashMap<>());
        ConditionOccurrence already = named.putIfAbsent(part, met(written));
        if (already != null) {
            throw new IllegalStateException(
                    "this reading has already named arm " + part + " of a fork: " + already);
        }
        return named.get(part);
    }

    /**
     * Where a report about the condition {@code met} points, it having been written as
     * {@code construct} at {@code at}.
     *
     * <p>The writing module answers where it wrote a construct of its own that a reader can open.
     * Everything else — a construct this compiler composed, a condition of a shape the reading has
     * no words for, code in a file this compilation does not hold — is placed by this reading,
     * which is the only thing that met it.
     */
    ConditionReportAnchor anchorOf(SourceConstructOrigin construct, SourcePos at,
                                   ConditionOccurrence met) {
        Citation where = Citation.of(at);
        if (where instanceof Citation.Written && construct != null && construct.isWritten()) {
            return new ConditionReportAnchor.WhereItIsWritten(
                    new WrittenCondition.Construct(construct));
        }
        return metHere(met, where);
    }

    /** The same, for reaching one arm of a fork the source wrote as {@code fork}. */
    ConditionReportAnchor anchorOfArm(SourceConstructOrigin fork, int part, SourcePos at,
                                      ConditionOccurrence met) {
        Citation where = Citation.of(at);
        if (where instanceof Citation.Written && fork != null && fork.isWritten()) {
            return new ConditionReportAnchor.WhereItIsWritten(
                    new WrittenCondition.ForkArm(fork, part));
        }
        return metHere(met, where);
    }

    /** An address of this reading, with the place it addresses written down in the same act. */
    private ConditionReportAnchor metHere(ConditionOccurrence met, Citation where) {
        metAt.put(met, where);
        return new ConditionReportAnchor.WhereTheReadingMetIt(module, met);
    }

    /** Where this reading met each condition it places itself. */
    Map<ConditionOccurrence, Citation> metAt() {
        return Collections.unmodifiableMap(new LinkedHashMap<>(metAt));
    }

    /**
     * {@code entries}, filed as what {@code condition} put on the way.
     *
     * <p>Filed by the entry itself and not by what it says. An entry is a value, and two copies of
     * a helper on two ways that never meet can put equal values on them; filed by the value, a way
     * through one would be told it met the other. What each way met is read off its own entries
     * when the way is recorded ({@link #saidOnTheWay}), and this is how it can be.
     *
     * @return {@code entries}, so a walk files what it puts on the way where it puts it
     */
    List<OnTheWay> said(ConditionOccurrence condition, List<OnTheWay> entries) {
        ModelOccurrence copy = stands.get(condition);
        if (copy != null) {
            file(entries, copy);
        }
        return entries;
    }

    /** The same, for entering an arm of a fork written as {@code fork}. */
    List<OnTheWay> saidEntering(ConstructOccurrence fork, List<OnTheWay> entries) {
        if (fork.isWritten()) {
            ModelOccurrence.statedAt(fork).ifPresent(copy -> file(entries, copy));
        }
        return entries;
    }

    private void file(List<OnTheWay> entries, ModelOccurrence copy) {
        for (OnTheWay each : entries) {
            madeBy.putIfAbsent(each, copy);
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> file(one, copy));
            }
        }
    }

    /**
     * Which copies put each of {@code ways}' entries on them, read off the entries themselves.
     *
     * <p>The ways one line is reached by, and no other: an entry is told the copy that made it,
     * and two equal entries on these ways made by two copies are told both.
     */
    SaidOnTheWay saidOnTheWay(List<List<OnTheWay>> ways) {
        Map<OnTheWay, List<ModelOccurrence>> entries = new LinkedHashMap<>();
        for (List<OnTheWay> way : ways) {
            told(way, entries);
        }
        return new SaidOnTheWay(entries, Map.of(), Map.of());
    }

    private void told(List<OnTheWay> way, Map<OnTheWay, List<ModelOccurrence>> into) {
        for (OnTheWay each : way) {
            ModelOccurrence copy = madeBy.get(each);
            if (copy != null) {
                List<ModelOccurrence> copies = into.computeIfAbsent(each, _ -> new ArrayList<>());
                if (!copies.contains(copy)) {
                    copies.add(copy);
                }
            }
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> told(one, into));
            }
        }
    }
}
