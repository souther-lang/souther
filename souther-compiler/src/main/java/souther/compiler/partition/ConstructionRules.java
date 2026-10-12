package souther.compiler.partition;

import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.RuleRoots;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The rules a value composed under one parameter is held to, asked by where it is written.
 *
 * <p>Every value whose rules reach a position, and not only the parameter's. A field of a case is a
 * field of that case's record, and the record's clauses — its own and every one it spreads — relate
 * it to the fields beside it; a field of an element is held to the element's clauses the same way.
 * Asked of the parameter alone, such a field is one no clause names, so a value fixed beside it is
 * chosen against nothing and every row built there breaks the clause relating the two.
 *
 * <p><b>Which values those are is the reading's answer</b> ({@link RuleRoots#naming}), and so is
 * which of them hold: only the case the value was narrowed to and only an element that stands. The
 * name a case shares with its sum goes on to the value above as well, so a clause written there is
 * kept beside the case's own rather than replaced by it.
 *
 * <p><b>Each value's rules are read on their own and the answers met.</b> What every one of them
 * leaves a position is an over-approximation of the values a row may write there, so the values
 * they all leave are too: meeting the answers narrows by each clause without ever taking out a value
 * one of them admits. What it does not do is reason across two values' clauses at once, which no
 * reading here is asked to.
 *
 * <p>Two ways of taking what is fixed in, because the searches that ask differ in when it is fixed.
 * What the caller settled before anything was chosen is read in with the rules
 * ({@link #valuesAt}, {@link #heldAt}); what a search fixes one position at a time is taken onto
 * the rules read with nothing settled ({@link #limitsAt}), which is what lets one reading serve every
 * branch of it.
 *
 * <p>One of these per value composed. What it keeps is true under the parameter and the caller's
 * settling, and both are fixed when it is made.
 */
final class ConstructionRules {

    private final MeasuredInput subject;
    private final RuleReadingContext reading;
    private final Map<TermPath, Place> settled;
    /** Each value's rules with the caller's settling read in, by where the value stands. */
    private final Map<TermPath, FieldDomains> readSettled = new HashMap<>();
    /** Each value's rules with nothing settled, which a search's settling is taken onto. */
    private final Map<TermPath, FieldDomains> readBare = new HashMap<>();
    private final Map<Taken, FieldDomains.Composing> composed = new HashMap<>();

    private ConstructionRules(MeasuredInput subject, Map<TermPath, Place> settled) {
        this.subject = subject;
        this.reading = subject.ruleReading();
        this.settled = new LinkedHashMap<>(settled);
    }

    /**
     * The rules a value composed for {@code subject} is held to, with {@code settled} read in.
     *
     * @param settled what the caller fixed before anything is chosen, at any parameter: a position no
     *                value's rules here name settles nothing here
     */
    static ConstructionRules of(MeasuredInput subject, Map<TermPath, Place> settled) {
        return new ConstructionRules(subject, settled);
    }

    /**
     * Where the value at {@code path} stops, met over every value whose rules name it, or null where
     * none of them stops it.
     */
    NumericDomain.Bounds valuesAt(TermPath path) {
        NumericDomain.Bounds out = null;
        for (RuleRoots.Naming each : namingOf(path)) {
            out = meet(out, settledRead(each).at(each.address().key()).bounds());
        }
        return out;
    }

    /**
     * How many the value at {@code path} holds, met over every value whose rules count it, or null
     * where none of them does.
     */
    FieldDomains.Held heldAt(TermPath path) {
        FieldDomains.Held out = null;
        for (RuleRoots.Naming each : namingOf(path)) {
            out = meet(out, settledRead(each).heldAt(each.address().key()));
        }
        return out;
    }

    /**
     * What each value naming {@code path} has had fixed under it, out of {@code chosen}: the key a
     * search asking {@link #limitsAt} under the same fixings would ask by, and the only part of
     * {@code chosen} the answer turns on.
     */
    Settling settlingAt(TermPath path, Map<TermPath, Place> chosen) {
        List<Map<RuleKey, Count>> out = new ArrayList<>();
        for (RuleRoots.Naming each : namingOf(path)) {
            out.add(fixedUnder(each.address().root(), chosen));
        }
        return new Settling(out);
    }

    /**
     * What can stand at {@code path} once {@code settling} is taken onto the rules of each value
     * naming it, met over all of them.
     */
    FieldDomains.ConstructionLimits limitsAt(TermPath path, Settling settling) {
        List<RuleRoots.Naming> named = namingOf(path);
        NumericDomain.Bounds values = null;
        FieldDomains.Held held = null;
        for (int i = 0; i < named.size(); i++) {
            RuleRoots.Naming each = named.get(i);
            FieldDomains.ConstructionLimits here = composedUnder(each, settling.fixed().get(i))
                    .at(each.address().key());
            values = meet(values, here.values());
            held = meet(held, here.held());
        }
        return new FieldDomains.ConstructionLimits(values, held);
    }

    /**
     * What a search has fixed under each value naming one position, in the order those values name
     * it. Compared as that, which is what makes it a key for what the position can take.
     */
    record Settling(List<Map<RuleKey, Count>> fixed) {

        Settling {
            fixed = List.copyOf(fixed);
        }
    }

    /**
     * The rules of a value, the way {@code reading} reads them: a record's clauses and every one it
     * spreads, and nothing for a value that has none of its own to read.
     *
     * <p>One reading of the value, not one per record inside it. A clause on the outer record says
     * what is left for a position two levels down, and a reading rebuilt at the inner record has
     * never seen it.
     *
     * <p>Read with what the walk that read the inputs has already made of these declarations.
     * Settling a coordinate is what makes each of these a reading of its own, but what the
     * declaration's string rules come to is settled by the rules and not by what is fixed beside
     * them, so a reading here that borrowed nothing would build every one of those machines again
     * for each value probed.
     */
    private static FieldDomains rulesOf(Type type, RuleReadingContext reading,
                                        Map<RuleKey, Count> settled) {
        RuleReadingSource source = reading.source();
        // Whether the position is a record, and which record, are one answer and it is the
        // reading's. The rules are then read on the name the value is written under where it wraps
        // that record, whose reading reaches the record's own rules and names its fields as the
        // record does, and on the record where it is written bare.
        if (!(TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                source.sums())
                instanceof Shape.Product(TypeSymbol.AtModule declared, Map<String, Type> _))) {
            return FieldDomains.NONE;
        }
        return FieldDomains.of(Partitions.rulesOver(type, declared, source), reading, settled);
    }

    private List<RuleRoots.Naming> namingOf(TermPath path) {
        return subject.rulesNaming(path);
    }

    private FieldDomains settledRead(RuleRoots.Naming value) {
        TermPath root = value.address().root();
        return readSettled.computeIfAbsent(root,
                at -> rulesOf(value.value(), reading, fixedUnder(at, settled)));
    }

    private FieldDomains.Composing composedUnder(RuleRoots.Naming value,
                                                 Map<RuleKey, Count> fixed) {
        TermPath root = value.address().root();
        return composed.computeIfAbsent(new Taken(root, fixed),
                taken -> readBare.computeIfAbsent(root,
                                at -> rulesOf(value.value(), reading, Map.of()))
                        .composing(FieldDomains.atValues(fixed)));
    }

    /** One value's rules with one settling taken on, which is what the same answer is to. */
    private record Taken(TermPath root, Map<RuleKey, Count> fixed) {}

    /**
     * The numbers among {@code fixed} that the rules of the value at {@code root} name, by what they
     * call each. A position those rules do not reach settles nothing in them, and the value itself
     * is no coordinate of its own rules.
     *
     * <p>In the order they were fixed, which is the caller's and the same on every run: the rules
     * take each settling in turn, and an order a hash gave would be one more thing a run decides.
     */
    private Map<RuleKey, Count> fixedUnder(TermPath root, Map<TermPath, Place> fixed) {
        Map<RuleKey, Count> out = new LinkedHashMap<>();
        fixed.forEach((path, at) -> {
            if (!(at instanceof Count number)) {
                return;
            }
            for (RuleRoots.Naming each : namingOf(path)) {
                RuleKey key = each.address().key();
                if (each.address().root().equals(root) && !key.isTheValueItself()) {
                    out.put(key, number);
                }
            }
        });
        return Collections.unmodifiableMap(out);
    }

    private static NumericDomain.Bounds meet(NumericDomain.Bounds one, NumericDomain.Bounds other) {
        return one == null ? other : other == null ? one : one.meet(other);
    }

    /** Both values' answers: how many the two leave together, and every run either keeps the
     *  elements apart at. */
    private static FieldDomains.Held meet(FieldDomains.Held one, FieldDomains.Held other) {
        if (one == null || other == null) {
            return one == null ? other : one;
        }
        List<List<String>> apart = new ArrayList<>(one.keptApart());
        apart.addAll(other.keptApart());
        return new FieldDomains.Held(one.bounds().meet(other.bounds()), List.copyOf(apart));
    }
}
