package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.test.ClosedWorldContract;
import souther.test.Nightly;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Reading a declaration with a coordinate settled and taking the settling onto a reading already
 * made answer the same thing about building a value.
 *
 * <p>What a search choosing one position at a time asks for at each of them is where the value
 * there stops and how many it holds, both under whatever the positions before it took. Those two
 * are the whole of what the rules give it. Read a declaration per position and they are answered by
 * a reading made under the settling; taken onto a reading made once, they are answered by a
 * projection of the constraints that reading came to — and this is the statement that the two are
 * the same question.
 *
 * <p>The statement is what lets one reading serve a whole search. Without it a search that read the
 * declaration once would be answering about the rules as they stood before it chose anything, which
 * is the reading that leaves {@code b} its whole range while {@code a < b} is still open.
 *
 * <p>Asked once a night. The two sides are compared at every position of every model this
 * repository carries, and the side that reads per settling builds the regex machines of every
 * declaration again for each settling, which is what the comparison is about and so cannot be
 * shared between the sides. Lending the machines across declarations would make the run cheaper by
 * changing how much a {@code Meter} has spent, and that is observable, so it is not a saving this
 * test may take. A disagreement between the two readings is found by the morning, on the branch a
 * change landed on.
 */
@ClosedWorldContract
@Nightly
class ASettlingReadAgainAndASettlingTakenOnLeaveTheSameConstructionLimitsTest {

    /**
     * Every record the models reach, every settling of one or two of its coordinates.
     *
     * <p>The settlings are taken from what each coordinate's own reading leaves it, plus the two
     * numbers any counted position can take. A pair as well as a single, because a rule relating two
     * positions says nothing until one of them is fixed and the whole point of settling one at a
     * time is what it leaves the other.
     */
    @Test
    void everySettlingLeavesWhatAReadingUnderItLeaves() {
        int compared = 0;
        int stopped = 0;
        int counted = 0;
        int deep = 0;
        for (Record record : recordsRead()) {
            RuleReadingContext reading =
                    RuleReadingContext.of(record.source(), record.policy(), record.lent());
            FieldDomains base = FieldDomains.of(record.declared(), reading);
            List<RuleKey> coordinates = coordinatesOf(base, record.fields());
            for (Map<RuleKey, Count> settling : settlings(base, coordinates)) {
                FieldDomains readUnder = FieldDomains.of(record.declared(), reading, settling);
                FieldDomains.Composing takenOn = base.composing(named(settling));
                for (RuleKey field : coordinates) {
                    NumericDomain.Bounds values = readUnder.at(field).bounds();
                    FieldDomains.Held held = readUnder.heldAt(field);
                    FieldDomains.ConstructionLimits limits = takenOn.at(field);
                    assertEquals(values, limits.values(),
                            () -> "where " + record.declared() + " is read with " + settling
                                    + " settled, `" + field + "` stops where the same settling "
                                    + "taken onto one reading says it stops");
                    assertEquals(held, limits.held(),
                            () -> "where " + record.declared() + " is read with " + settling
                                    + " settled, `" + field + "` holds what the same settling "
                                    + "taken onto one reading says it holds");
                    compared++;
                    stopped += values == null ? 0 : 1;
                    counted += held == null ? 0 : 1;
                    deep += field.steps().size() > 1 ? 1 : 0;
                }
            }
        }
        assertFalse(compared == 0,
                "no record of any model this repository carries was compared, so this holds by "
                        + "asking nothing");
        // And that what was compared says something. Two readings agreeing that nothing is known
        // about every coordinate is an agreement either of them could reach by answering nothing,
        // and it is the answer a projection that read the wrong state would give.
        assertFalse(stopped == 0, "no coordinate was stopped anywhere, so every comparison above "
                + "was of one absent range against another");
        assertFalse(counted == 0, "no coordinate was counted, so nothing above compared what a "
                + "position holds");
        // And that a name reaching below a field was among them. A clause names a position at
        // whatever depth it can reach, and a population that had come to hold only the shallowest
        // of them would go on passing while saying it compared every coordinate.
        assertFalse(deep == 0, "no coordinate below a field was compared, so nothing above says "
                + "the two derivations agree about the names a clause reaches through");
        System.out.println("construction limits compared: " + compared + ", of them " + stopped
                + " stopped, " + counted + " counted and " + deep + " named below a field");
    }

    /**
     * One record declaration, read where its rules are, with what its model already knows.
     *
     * <p>The lender is the model's and not this record's. Where a set's strings stop is settled by
     * the set, so it is the same answer under every declaration of one model and under every
     * settling asked of one declaration — and a reading handed nothing walks it again for each of
     * them. What is lent is that knowledge and nothing else: a reading of the declaration is what
     * this compares, so neither derivation is handed one.
     */
    private record Record(TypeSymbol.AtModule declared, RuleReadingSource source,
                          ReadingPolicy policy, Map<String, Type> fields,
                          DeclarationReadings lent) {}

    /**
     * The coordinates of one record that are asked about.
     *
     * <p>Taken from the reading and not from the fields the type declares. A clause of a record
     * names positions at whatever depth it can reach — {@code interval.startsAt} is one name and
     * not two — so the names a search settles and asks under are the reading's own, and a
     * population built by walking the fields one step at a time would compare only the shallowest
     * of them while saying it compared every one.
     *
     * <p>The declared fields as well, which the reading has no entry for where no rule reaches
     * them. A position nothing is written about is one both derivations must still answer alike
     * about, and it is the answer a projection reading the wrong state gives most easily.
     */
    private static List<RuleKey> coordinatesOf(FieldDomains rules, Map<String, Type> fields) {
        Set<RuleKey> out = new LinkedHashSet<>();
        fields.keySet().forEach(field -> out.add(RuleKey.of(field)));
        rules.placed().forEach(placed -> out.add(placed.path()));
        rules.stated().forEach(placed -> out.add(placed.path()));
        out.remove(RuleKey.THE_VALUE);
        return List.copyOf(out);
    }

    /**
     * The settlings asked about: each coordinate at each value it could take, and each pair of them
     * at the first value each could.
     */
    private static List<Map<RuleKey, Count>> settlings(FieldDomains base, List<RuleKey> fields) {
        Map<RuleKey, List<Count>> take = new LinkedHashMap<>();
        for (RuleKey field : fields) {
            take.put(field, values(base.at(field).bounds()));
        }
        List<Map<RuleKey, Count>> out = new ArrayList<>();
        for (RuleKey field : fields) {
            for (Count at : take.get(field)) {
                out.add(Map.of(field, at));
            }
        }
        for (int i = 0; i < fields.size(); i++) {
            for (int j = i + 1; j < fields.size(); j++) {
                List<Count> one = take.get(fields.get(i));
                List<Count> other = take.get(fields.get(j));
                if (one.isEmpty() || other.isEmpty()) {
                    continue;
                }
                Map<RuleKey, Count> both = new LinkedHashMap<>();
                both.put(fields.get(i), one.get(0));
                both.put(fields.get(j), other.get(0));
                out.add(both);
            }
        }
        return out;
    }

    /** What one coordinate is settled at: where its own rules stop it, and the two numbers a
     *  coordinate with no end still takes. */
    private static List<Count> values(NumericDomain.Bounds bounds) {
        Set<Count> out = new LinkedHashSet<>();
        out.add(new Count(BigDecimal.ZERO));
        out.add(new Count(BigDecimal.ONE));
        if (bounds != null) {
            end(bounds.min(), out);
            end(bounds.max(), out);
        }
        return List.copyOf(out);
    }

    private static void end(Endpoint endpoint, Set<Count> out) {
        if (endpoint != null && endpoint.at() instanceof Count at) {
            out.add(at);
        }
    }

    /** The same settling as the names a reading of the value writes it under. */
    private static Map<NumberAt<RuleKey>, Count> named(Map<RuleKey, Count> settling) {
        Map<NumberAt<RuleKey>, Count> out = new LinkedHashMap<>();
        settling.forEach((field, at) -> out.put(NumberAt.valueOf(field), at));
        return out;
    }

    /** Every record every behavior of every model this repository carries reads, and the ones
     *  under them. */
    private static List<Record> recordsRead() {
        List<Record> out = new ArrayList<>();
        for (Compilation compilation : RepositoryModels.all()) {
            ReadingPolicy policy = compilation.db().ask(new Front.Reading()).value();
            DeclarationReadings lent = RepositoryModels.knownTo(compilation);
            for (String module : compilation.modules()) {
                RuleReadingSource source = RuleReadings.of(compilation, module);
                Set<TypeSymbol> seen = new LinkedHashSet<>();
                for (DeclaredSig declared
                        : compilation.db().ask(new Bodies.DeclaredSignatures(module)).value()
                                .values()) {
                    for (DeclaredSig.Input input : declared.inputs()) {
                        under(input.type(), source, policy, lent, seen, out);
                    }
                }
            }
        }
        return out;
    }

    /**
     * Every record a value of {@code type} can hold, however it is reached.
     *
     * <p>Through the cases of a sum, through what a collection holds and through what stands under
     * an optional as well as through a record's fields. A search composing a value reaches a
     * declaration by every one of these, so a walk that followed fields alone would leave out the
     * records only a case or an element leads to and would say it had walked them.
     */
    private static void under(Type type, RuleReadingSource source, ReadingPolicy policy,
                              DeclarationReadings lent, Set<TypeSymbol> seen, List<Record> out) {
        Shape shape = TypeView.asWritten(type, source.symbols(), source.published()).shape();
        switch (shape) {
            case Shape.Product(TypeSymbol name, Map<String, Type> fields) -> {
                if (!(name instanceof TypeSymbol.AtModule declared) || !seen.add(declared)) {
                    return;
                }
                if (!fields.isEmpty()) {
                    out.add(new Record(declared, source, policy, fields, lent));
                }
                fields.values().forEach(field -> under(field, source, policy, lent, seen, out));
            }
            case Shape.Cases(Set<TypeSymbol> members) ->
                    members.forEach(each ->
                            under(Type.ref(each), source, policy, lent, seen, out));
            case Shape.Sequence(var _, Type element) ->
                    under(element, source, policy, lent, seen, out);
            case Shape.Optional(Type element) -> under(element, source, policy, lent, seen, out);
            case Shape.Mapping(Type key, Type value) -> {
                under(key, source, policy, lent, seen, out);
                under(value, source, policy, lent, seen, out);
            }
            case Shape.Tuple(List<Type> elements) ->
                    elements.forEach(each -> under(each, source, policy, lent, seen, out));
            default -> { }
        }
    }
}
