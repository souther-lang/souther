package souther.compiler.partition;

import souther.compiler.check.FieldDomains;
import souther.compiler.check.PlacesTheRulesRead;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeOps;
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
 * <p>What is fixed is taken onto the rules read with nothing settled, whoever fixed it: the caller
 * before anything was chosen ({@link #valuesAt}, {@link #heldAt}) or a search one position at a
 * time ({@link #limitsAt}). Taking a number onto a reading states the same equality the reading
 * states when it is handed one ({@link FieldDomains#composing}), so the declaration is read once
 * whatever values a search goes on to fix, and not once for each of them.
 *
 * <p>One of these per value composed. What it keeps is true under the parameter and the caller's
 * settling, and both are fixed when it is made.
 */
final class ConstructionRules {

    private final MeasuredInput subject;
    private final RuleReadingContext reading;
    private final Map<TermPath, Place> settled;
    /** Each value's rules with nothing settled, which every settling is taken onto. */
    private final Map<TermPath, FieldDomains> readBare = new HashMap<>();
    private final Map<Taken, FieldDomains.Composing> composed = new HashMap<>();
    /** The places each value's rules read, by where the value stands. */
    private final Map<TermPath, PlacesTheRulesRead> readAt = new HashMap<>();

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
        return limitsAt(path).values();
    }

    /**
     * How many the value at {@code path} holds, met over every value whose rules count it, or null
     * where none of them does.
     */
    FieldDomains.Held heldAt(TermPath path) {
        return limitsAt(path).held();
    }

    /**
     * Everything the rules leave the value at {@code path} with what the caller settled read in,
     * as one answer: a caller wanting both where the value stops and how many it holds asks once,
     * since each is a reading of every rule naming the position.
     */
    FieldDomains.ConstructionLimits limitsAt(TermPath path) {
        return limitsAt(path, settlingAt(path, settled));
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
        // Every value naming the position, met: a gap one value's rules leave is a gap in the
        // position, and a value leaving it nothing leaves the position nothing.
        FieldDomains.ConstructionLimits limits = FieldDomains.ConstructionLimits.NONE;
        for (int i = 0; i < named.size(); i++) {
            RuleRoots.Naming each = named.get(i);
            limits = limits.meet(composedUnder(each, settling.fixed().get(i))
                    .at(each.address().key()));
        }
        return limits;
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
     * <p>With nothing settled, which is the declaration's own reading and the one the walk that read
     * the inputs has already made: asked again here, it is borrowed rather than read.
     */
    private static FieldDomains rulesOf(Type type, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        // Whether the position is a record, and which record, are one answer and it is the
        // reading's. The rules are then read on the name the value is written under where it wraps
        // that record, whose reading reaches the record's own rules and names its fields as the
        // record does, and on the record where it is written bare.
        if (TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                source.sums())
                instanceof Shape.Product(TypeSymbol.AtModule declared, Map<String, Type> _)) {
            return FieldDomains.of(Partitions.rulesOver(type, declared, source), reading);
        }
        // And a name wrapped round a value with no fields, whose rules are about the value itself:
        // which class they hold it to is what a builder choosing it has to know, as it is for a
        // field, and is read on the outermost name as every other rule the value wears is.
        return TypeOps.outermost(type, source.inners()) instanceof TypeOps.Unwrapped worn
                && worn.layer().named() instanceof TypeSymbol.AtModule name
                ? FieldDomains.of(name, reading) : FieldDomains.NONE;
    }

    /**
     * The constant, as the fold reads one, written at {@code path} where a rule of a value it is in
     * ties it to other places, in a value of those places that holds what {@code fixed} puts at
     * any of them ({@link FieldDomains#writtenTogether}) — or null where none is.
     *
     * <p>A value of the places such a rule ties together is one value of all of them, which the
     * limits each place is chosen in cannot say: a rule relating two strings leaves no one of them
     * a set. So each of those places offers its part of it, and the parts make the one value —
     * of the values already at the rest, and not of a value found with nothing there.
     *
     * @param fixed the constants, as the fold reads one, already at other positions
     */
    Object writtenTogetherAt(TermPath path, Map<TermPath, Object> fixed) {
        for (RuleRoots.Naming each : namingOf(path)) {
            TermPath root = each.address().root();
            Map<RuleKey, Object> held = new LinkedHashMap<>();
            fixed.forEach((at, value) -> {
                for (RuleRoots.Naming other : namingOf(at)) {
                    if (other.address().root().equals(root)) {
                        held.put(other.address().key(), value);
                    }
                }
            });
            Object written = bare(each).writtenTogether(each.address().key(), held)
                    .get(each.address().key());
            if (written != null) {
                return written;
            }
        }
        return null;
    }

    /**
     * Whether a value whose rules name {@code here} says something of a position strictly under it.
     *
     * <p>What a plan asks before choosing a value whole at {@code here}. A value chosen whole is
     * composed by its own declaration's rules, and a rule of a value above it about a field under
     * it — a name a sum's cases share — is not one of those: the value comes back holding whatever
     * its own rules leave that field, and every row built at it is refused by the rule above. Laid
     * out as positions instead, each field is a position {@link #limitsAt} meets every naming at.
     */
    boolean speaksUnder(TermPath here) {
        for (RuleRoots.Naming each : namingOf(here)) {
            if (placesRead(each).readUnder(each.address().key())) {
                return true;
            }
        }
        return false;
    }

    /** The places the rules of the value {@code value} names a position in read. */
    private PlacesTheRulesRead placesRead(RuleRoots.Naming value) {
        return readAt.computeIfAbsent(value.address().root(),
                at -> PlacesTheRulesRead.of(value.value(), reading.source()));
    }

    private List<RuleRoots.Naming> namingOf(TermPath path) {
        return subject.rulesNaming(path);
    }

    /** The rules of the value {@code value} names a position in, with nothing settled. */
    private FieldDomains bare(RuleRoots.Naming value) {
        return readBare.computeIfAbsent(value.address().root(),
                at -> rulesOf(value.value(), reading));
    }

    private FieldDomains.Composing composedUnder(RuleRoots.Naming value,
                                                 Map<RuleKey, Count> fixed) {
        TermPath root = value.address().root();
        return composed.computeIfAbsent(new Taken(root, fixed),
                taken -> bare(value).composing(FieldDomains.atValues(fixed)));
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

}
