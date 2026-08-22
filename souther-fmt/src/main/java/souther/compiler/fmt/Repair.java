package souther.compiler.fmt;

import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The source with what the canonical form has at the units a witness names.
 *
 * <p>Composed and projected once. A witness owns no patch — two of them land on one line of the
 * canonical form often enough that this is not hypothetical — and a repair applied one at a time
 * would rewrite a line and then apply the next at an offset that line no longer has. So every
 * expectation is turned into what it says about a stretch of the source, the stretches are held
 * against each other, and the text is written once.
 *
 * <p>Every family {@link Witness} has is composed here, and the switch below is exhaustive over it
 * rather than defaulting: a rule whose expectation is added without being composed would answer with
 * a text that is not the canonical form and say nothing about having done so, and the compiler is a
 * better place to hold that than a run.
 */
final class Repair {

    private Repair() {
    }

    /** One stretch of the source, and what the canonical form has instead. */
    record Edit(int from, int to, String text) {}

    /**
     * A source and its canonical form, with what every witness of one round would ask of them read
     * once.
     *
     * <p>Two of the projections ask a question the round shares, and each of them asks it of a whole
     * file to answer about one unit. A group's witness is about the opportunities that group
     * settles, and a layout has one at every place any group could break; a level's witness is about
     * the lines written under that level, and the canonical form's lines are the whole file's. Asked
     * per witness, both read everything — so a round over a source that departs at a large fraction
     * of its groups cost the witnesses multiplied by the file, when what the round is about is one
     * departure per witness.
     *
     * <p>So each is gathered under the unit that is asked about. What a witness reads is then its
     * own unit's, and what the projection reads is the file once.
     *
     * <p>Both here, though only one of them could be kept beside the layout. Which opportunities a
     * group settles is the layout's answer and nothing about a source; which lines are written under
     * a level is the canonical form's, but where the source begins each of them is not, and a
     * gathering holding that is about the pair. Split between the two places, a reader asking what a
     * projection reads once would have to find the answer in both.
     */
    record Round(String source, Formatter.CanonicalForm canonical, Witnesses.Pairing pairing,
            Map<Doc.GroupRef, List<Opportunity>> settling,
            Map<Doc.NestRef, List<Witnesses.CanonicalLine>> under,
            Map<Columns.Unit, List<Witnesses.CanonicalStop>> atAColumn) {

        Round(String source, Formatter.CanonicalForm canonical, Witnesses.Pairing pairing) {
            this(source, canonical, pairing, settling(canonical.layout()),
                    under(Witnesses.lines(source, canonical, pairing)),
                    atAColumn(canonical, pairing));
        }

        /**
         * The canonical form's stops, gathered under the column each is written to.
         *
         * <p>The third of these, and the same reason as the other two: what a column's repair is
         * about is the rows written to that column, and asked per witness it would read the whole
         * file once for each column the file has.
         */
        private static Map<Columns.Unit, List<Witnesses.CanonicalStop>> atAColumn(
                Formatter.CanonicalForm canonical, Witnesses.Pairing pairing) {
            Map<Columns.Unit, List<Witnesses.CanonicalStop>> out = new LinkedHashMap<>();
            for (Witnesses.CanonicalStop stop
                    : Witnesses.stops(canonical, pairing.writesCode())) {
                out.computeIfAbsent(stop.occurrence().unit(), _ -> new ArrayList<>()).add(stop);
            }
            return out;
        }

        /**
         * The layout's opportunities, gathered under the group whose decision settles each.
         *
         * <p>By identity, which is how a group is asked for everywhere else: a {@link Doc.GroupRef}
         * is the group and not a description of one, and two of them are the same group exactly
         * where they are the same reference.
         */
        private static Map<Doc.GroupRef, List<Opportunity>> settling(Layout layout) {
            Map<Doc.GroupRef, List<Opportunity>> out = new IdentityHashMap<>();
            for (Opportunity o : layout.opportunities()) {
                out.computeIfAbsent(o.settledBy(), _ -> new ArrayList<>()).add(o);
            }
            return out;
        }

        /**
         * The canonical form's lines, gathered under every level each is written under and not only
         * the innermost.
         *
         * <p>That is what the indentation repair asks for: a level that moves takes what is nested
         * inside it along, so the lines it writes are the ones written anywhere under it. Each line
         * therefore stands under as many entries as it has levels, and what a level's witness reads
         * is its own entry rather than the file.
         *
         * <p>In the order the canonical form writes them, which the repair rests on: it keeps the
         * first line it meets at each of the source's line starts, and the order it meets them in is
         * the order they are written.
         */
        private static Map<Doc.NestRef, List<Witnesses.CanonicalLine>> under(
                List<Witnesses.CanonicalLine> lines) {
            Map<Doc.NestRef, List<Witnesses.CanonicalLine>> out = new IdentityHashMap<>();
            for (Witnesses.CanonicalLine line : lines) {
                for (Doc.NestRef level : line.under()) {
                    out.computeIfAbsent(level, _ -> new ArrayList<>()).add(line);
                }
            }
            return out;
        }
    }

    /**
     * {@code source} with the expectations of {@code witnesses} written into it.
     *
     * <p>Refuses two expectations over one stretch rather than letting the later win. Two rules
     * answering about the same characters would be a conflict the model says is not there, and
     * finding one is worth more than a text.
     */
    static String repair(String source, Formatter.CanonicalForm canonical,
            List<Witness> witnesses) {
        return apply(source,
                edits(source, canonical, new Witnesses.Pairing(source, canonical), witnesses));
    }

    /**
     * The stretches the expectations of {@code witnesses} come to, composed and in the order they
     * are written.
     *
     * <p>Separate from writing them so that a caller can say where the text it is now looking at
     * came from. The report asks the rules again after a repair — a rule that reads another's
     * result has nothing to say until that one is answered — and a deviation found in the second
     * text is about a place in the first.
     */
    static List<Edit> edits(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing, List<Witness> witnesses) {
        return composed(each(source, canonical, pairing, witnesses));
    }

    /**
     * The stretches each of {@code witnesses} comes to on its own, in the same order as the
     * witnesses.
     *
     * <p>Kept apart from the composition so that a caller who wants both gets one projection. What
     * a report wants of a witness besides its expectation is where in the source it lands, which is
     * where the first stretch it comes to begins — and asked for on its own that was the whole
     * projection evaluated to keep one number, and then evaluated again to write the text.
     */
    static List<List<Edit>> each(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing, List<Witness> witnesses) {
        Round round = new Round(source, canonical, pairing);
        List<List<Edit>> out = new ArrayList<>();
        for (Witness w : witnesses) {
            out.add(of(round, w));
        }
        return out;
    }

    /** The stretches of {@code each}, composed and in the order they are written. */
    static List<Edit> composed(List<List<Edit>> each) {
        List<Edit> edits = new ArrayList<>();
        for (List<Edit> mine : each) {
            edits.addAll(mine);
        }
        edits.sort(Comparator.comparingInt(Edit::from)
                .thenComparing(Comparator.comparingInt(Edit::to).reversed()));
        List<Edit> out = new ArrayList<>();
        Edit last = null;
        for (Edit e : edits) {
            if (e.equals(last)) {
                continue;   // two levels, nested one inside the other, moving the same line the
                            // same way: one expectation about it and not two
            }
            if (last != null && e.from() >= last.from() && e.to() <= last.to()) {
                // A stretch inside another's. Two rules answering about their own units whose text
                // happens to overlap -- an indent and the break that writes the line it is on -- is
                // the composition this is here to do, so it is only a conflict where the wider one
                // does not already write what the narrower asks for.
                if (last.text().endsWith(e.text())) {
                    continue;
                }
                throw new IllegalStateException(
                        "two expectations over one stretch of the source at " + e.from()
                                + ", and they do not agree: [" + last.text() + "] against ["
                                + e.text() + "]");
            }
            if (last != null && e.from() < last.to()) {
                throw new IllegalStateException(
                        "two expectations over one stretch of the source, at " + e.from()
                                + "; the rules answer about their own units, and this is two of them"
                                + " answering about the same characters");
            }
            last = e;
            out.add(e);
        }
        return out;
    }

    /** {@code source} with {@code edits} written into it. */
    static String apply(String source, List<Edit> edits) {
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (Edit e : edits) {
            out.append(source, at, e.from()).append(e.text());
            at = e.to();
        }
        return out.append(source.substring(at)).toString();
    }

    /**
     * Where an offset of a repaired text stood in the text it was repaired from.
     *
     * <p>An offset inside a stretch a rule wrote over comes back as the start of that stretch: what
     * is there now was written by the repair, and where it came from is the whole of what it
     * replaced.
     */
    static int before(List<Edit> edits, int at) {
        int delta = 0;
        for (Edit e : edits) {
            int from = e.from() + delta;
            if (at < from) {
                break;
            }
            if (at < from + e.text().length()) {
                return e.from();
            }
            delta += e.text().length() - (e.to() - e.from());
        }
        return at - delta;
    }

    /**
     * The stretches of the source one witness is about, in the order they are written.
     *
     * <p>Empty where what it is about is written around a comment, which the rules about comments
     * have to say before anything can be written there.
     *
     * <p>Asked of a {@link Round} rather than of the two texts, so that what a witness is about is
     * found once for a whole round rather than once per witness. The two texts' tokens were the
     * first of those — a source with three hundred of them was parsed a thousand times to write one
     * text — and what a unit is asked of is the second.
     */
    static List<Edit> of(Round round, Witness w) {
        String source = round.source();
        Formatter.CanonicalForm canonical = round.canonical();
        Witnesses.Pairing pairing = round.pairing();
        return switch (w) {
            case Witness.BetweenTwoTokens b -> List.of(spacing(pairing, b));
            case Witness.Separation s -> List.of(separation(source, canonical, s));
            case Witness.Indentation i -> indentation(round, i);
            case Witness.Forced f -> switch (f.unit().adjacency()) {
                case -1 -> List.of(ending(source, canonical, pairing));
                case -2 -> List.of(aboveTheLastComment(source, canonical, pairing));
                default -> gaps(source, canonical, pairing, List.of(f.unit().adjacency()));
            };
            // One repair for two rules. Which of them a source is being held to is what the two
            // texts disagree about; what writes the canonical form is the same either way, since
            // a construct is put down the page by breaking the places it settles.
            case Witness.Conditional c -> gaps(source, canonical, pairing,
                    opportunitiesOf(round, c.unit().group()));
            case Witness.RunTogether r -> gaps(source, canonical, pairing,
                    opportunitiesOf(round, r.unit().group()));
            case Witness.Settled s ->
                    gaps(source, canonical, pairing, List.of(s.unit().adjacency()));
            case Witness.AtTheEndOfALine e -> List.of(new Edit(e.unit().at(),
                    e.unit().at() + e.source().length(), e.canonical()));
            case Witness.ACodeToken t -> List.of(new Edit(t.unit().at(),
                    t.unit().at() + t.source().length(), t.canonical()));
            case Witness.TrailingComment t -> List.of(new Edit(
                    t.unit().at() - t.source().length(), t.unit().at(), t.canonical()));
            case Witness.CommentAbove a -> List.of(under(source, a));
            case Witness.CommentCarrier c -> moved(source, canonical, pairing, c);
            case Witness.AtAColumn c -> columns(round, c);
        };
    }

    /**
     * The rows of one column, each carried out to it.
     *
     * <p>One edit per row and one decision behind them. What is written is the whole run before the
     * connector, which is this rule's: the spacing rule is not asked at a stop, so nothing else
     * answers about these characters.
     *
     * <p>The number of spaces is worked out from where the row has got to in the text being
     * repaired rather than from what the source had there, so a row whose own content is also being
     * repaired does not have to be written in any order. Where the row has got further than the
     * column, the run is the separator alone and the round after this one asks again — the width in
     * front of the connector is another rule's and it has not been written yet.
     */
    private static List<Edit> columns(Round round, Witness.AtAColumn witness) {
        String source = round.source();
        List<SyntaxToken> had = round.pairing().hadCode();
        List<Edit> out = new ArrayList<>();
        for (Witnesses.CanonicalStop stop
                : round.atAColumn().getOrDefault(witness.unit(), List.of())) {
            int i = stop.adjacency();
            int from = had.get(i).end();
            int to = had.get(i + 1).start();
            String between = source.substring(from, to);
            if (between.indexOf('\n') >= 0 || between.contains("//")) {
                continue;   // the source broke the row, or wrote a comment there
            }
            if (!Witnesses.padsWithSpaces(source, had.get(i), had.get(i + 1))) {
                continue;   // the spacing rule is writing this run, and two of us must not
            }
            String separator = stop.separator();
            if (separator.chars().anyMatch(c -> c != ' ')) {
                throw new IllegalStateException(
                        "a column stop whose separator is not spaces ([" + separator + "]); what is"
                                + " written before a connector is counted in columns here, and a"
                                + " tab is not one of them");
            }
            int reached = Witnesses.columnAt(source, from);
            int wide = Math.max(witness.canonical() - reached, separator.length());
            out.add(new Edit(from, to, " ".repeat(wide)));
        }
        return out;
    }

    /**
     * The columns the canonical form writes the lines of a level at.
     *
     * <p>One edit per line and one decision behind them, which is the shape the model asks for: the
     * expectation is composed over the levels and projected onto the text once. The column written
     * is the one the break was written at rather than the source's plus a step, so a level whose
     * outer level is also being moved does not have to be repaired in any order.
     *
     * <p>Every line written under the level and not only the ones written at it. A level that moves
     * takes what is nested inside it along, and those deeper levels have nothing against them —
     * their step is right and it is the column underneath that changed.
     *
     * <p>Asked of the level's own lines and not of the file's. {@link Round} gathers them under the
     * levels they are written under, so a source whose every level is indented wrongly reads each
     * level's lines once rather than the file once per level.
     */
    private static List<Edit> indentation(Round round, Witness.Indentation witness) {
        String source = round.source();
        List<Edit> out = new ArrayList<>();
        Set<Integer> at = new LinkedHashSet<>();
        for (Witnesses.CanonicalLine line
                : round.under().getOrDefault(witness.unit().inner(), List.of())) {
            if (line.sourceStart() == null || !at.add(line.sourceStart())) {
                continue;
            }
            int lineStart = line.sourceStart();
            int indent = lineStart;
            while (indent < source.length() && source.charAt(indent) == ' ') {
                indent++;
            }
            out.add(new Edit(lineStart, indent, " ".repeat(line.indent())));
        }
        return out;
    }

    /**
     * What the canonical form writes in the gaps at {@code adjacencies}.
     *
     * <p>The whole gap, since what a break rule says about one is that a line ends there and how
     * far in the next begins — the same characters the spacing rule answers for where no line ends.
     *
     * <p>A gap holding a comment on either side is left alone. Where a comment stands, what is
     * written around it is the comment rules' and copying the canonical form's text over would
     * write the comment twice or lose it.
     */
    private static List<Edit> gaps(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing, List<Integer> adjacencies) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        List<Edit> out = new ArrayList<>();
        for (int i : adjacencies) {
            if (i < 0 || i + 1 >= writes.size()) {
                continue;   // the file's own break, which has no token after it
            }
            String wrote = text.substring(writes.get(i).end(), writes.get(i + 1).start());
            String has = source.substring(had.get(i).end(), had.get(i + 1).start());
            if (wrote.contains("//") || has.contains("//")) {
                continue;
            }
            out.add(new Edit(had.get(i).end(), had.get(i + 1).start(), wrote));
        }
        return out;
    }

    /**
     * Which adjacencies of the canonical form the places a group settles differently stand at.
     *
     * <p>The ones the source settled the other way, and every one of them: the group's decision is
     * one and a source that took it at some of its places has still not taken it. A place the
     * source already ends a line at is left alone — what is still wrong there is how far in the
     * next line begins, which is the indentation rule's, and writing the canonical form's text over
     * it would be two rules over the same characters.
     *
     * <p>In the order they stand in, so that the first is the one the witness stands at. Where the
     * report says the source departed is the first place it did, and that has to be the same
     * question as which of them this writes first.
     *
     * <p>Asked of the group's own opportunities and not of the layout's. A layout has one at every
     * place any group could break, so a sweep of it per group is the whole file for one group's
     * question — and a source that departs at a large fraction of its groups is asked that as many
     * times as it has departed. Which opportunities a group settles is the layout's answer, and
     * {@link Round} has it once.
     */
    private static List<Integer> opportunitiesOf(Round round, Doc.GroupRef group) {
        List<Integer> out = new ArrayList<>();
        for (Opportunity o : round.settling().getOrDefault(group, List.of())) {
            if (Witnesses.brokeInSource(round.source(), round.pairing(), o.at()) == o.broke()) {
                continue;
            }
            int i = round.pairing().adjacencyAt(o.at());
            if (i >= 0) {
                out.add(i);
            }
        }
        out.sort(null);
        return out;
    }

    /**
     * The lines the canonical form ends between a comment and what it is written above.
     *
     * <p>To the start of the line the next thing is on, so that how far in that line begins is left
     * where it is: that is the indentation rule's and this one has nothing to say about it.
     */
    private static Edit under(String source, Witness.CommentAbove witness) {
        int from = source.indexOf('\n', witness.unit().at());
        int to = from;
        while (to < source.length() && Character.isWhitespace(source.charAt(to))) {
            to++;
        }
        while (to > from && source.charAt(to - 1) != '\n') {
            to--;
        }
        return new Edit(from, to, "\n".repeat(witness.canonical()));
    }

    /**
     * What the canonical form writes after its last code token: the one newline a file ends with.
     *
     * <p>The file's own break stands after everything, so there is no token on the far side of it
     * and the stretch runs to the end of the text. Left to {@link #gaps}, which pairs a boundary
     * with the two tokens it stands between, this one has no pair and was written nowhere — so the
     * rule was a value, the witness was made, and neither the report nor the repair had it.
     */
    private static Edit ending(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing) {
        String text = canonical.layout().text();
        int from = lastWritten(pairing.hadCode(), pairing.hadComments());
        int wrote = lastWritten(pairing.writesCode(), pairing.writesComments());
        if (from < 0 || wrote < 0) {
            return new Edit(source.length(), source.length(), "");
        }
        return new Edit(from, source.length(), text.substring(wrote));
    }

    /** What the canonical form writes between its last code token and the comment after it. */
    private static Edit aboveTheLastComment(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing) {
        String text = canonical.layout().text();
        String has = Witnesses.aboveTheLastComment(source, pairing.hadCode(),
                pairing.hadComments());
        String wrote = Witnesses.aboveTheLastComment(text, pairing.writesCode(),
                pairing.writesComments());
        List<SyntaxToken> code = pairing.hadCode();
        int from = code.isEmpty() ? 0 : code.get(code.size() - 1).end();
        return new Edit(from, from + has.length(), wrote);
    }

    /**
     * Where the last thing a text writes ends: its last code token, or the comment after it.
     *
     * <p>A comment can be the last thing in a file, and the file still ends with one newline. Taken
     * from the last code token alone, the stretch this rule writes would hold that comment and
     * either write over it or be left alone for holding one — and the file's own break would again
     * be a rule with a witness and nothing written for it.
     */
    private static int lastWritten(List<SyntaxToken> code, List<SyntaxToken> comments) {
        int at = -1;
        if (!code.isEmpty()) {
            at = code.get(code.size() - 1).end();
        }
        if (!comments.isEmpty()) {
            at = Math.max(at, comments.get(comments.size() - 1).end());
        }
        return at;
    }

    /**
     * The two stretches a comment moves between: the one it is written in and the one it is written
     * in in the canonical form.
     *
     * <p>Both are written as the canonical form has them, which is what moves it — the comment is
     * in one of the two there and in the other here, and writing each stretch as the canonical form
     * has it leaves it in exactly one. A comment is not cut out and pasted: the stretches say what
     * they hold, and the comment is part of what they hold.
     */
    private static List<Edit> moved(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing, Witness.CommentCarrier witness) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        List<Edit> out = new ArrayList<>();
        for (int i : new int[] {witness.canonical(), witness.source()}) {
            if (i < 0 || i + 1 >= writes.size()) {
                continue;
            }
            out.add(new Edit(had.get(i).end(), had.get(i + 1).start(),
                    text.substring(writes.get(i).end(), writes.get(i + 1).start())));
        }
        out.sort(Comparator.comparingInt(Edit::from));
        return out;
    }

    /** What the canonical form writes between the two tokens of a boundary. */
    private static Edit spacing(Witnesses.Pairing pairing, Witness.BetweenTwoTokens witness) {
        List<SyntaxToken> had = pairing.hadCode();
        int i = witness.unit().adjacency();
        return new Edit(had.get(i).end(), had.get(i + 1).start(), witness.canonical());
    }

    /**
     * The blank lines the canonical form writes between two items.
     *
     * <p>From the end of the line the first item is written on, and not from the end of the item.
     * An item with a comment after it ends before that comment — {@link Written#end} is its last
     * code token — and a stretch beginning there would put the blank lines in front of the comment
     * and leave the ones after it where they were.
     *
     * <p>It runs to the start of the line the next thing is written on, so a comment in the gap
     * stays where it is: it belongs to the second item and is not this rule's to move.
     */
    private static Edit separation(String source, Formatter.CanonicalForm canonical,
            Witness.Separation witness) {
        List<Written> before =
                canonical.construction().places().sourcesOf(witness.unit().previous());
        int from = source.indexOf('\n', before.get(before.size() - 1).end());
        if (from < 0) {
            throw new IllegalStateException(
                    "the item before a separation ends the file, so nothing is written after it");
        }
        int to = from;
        while (to < source.length() && Character.isWhitespace(source.charAt(to))) {
            to++;
        }
        while (to > from && source.charAt(to - 1) != '\n') {
            to--;
        }
        return new Edit(from, to, "\n".repeat(witness.canonical() + 1));
    }
}
