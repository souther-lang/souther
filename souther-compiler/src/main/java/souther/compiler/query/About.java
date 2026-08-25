package souther.compiler.query;

import souther.compiler.types.TypeSymbol;

/**
 * What one {@link Adequacy.Finding} is about.
 *
 * <p>The value a measure established, handed on as itself. Not the arguments of a sentence: a
 * finding used to carry {@code List<Object>} in the order a message key took them, so what each
 * element was followed from the kind and from nothing written down, and every reader indexed into it
 * and cast. Two defects came out of that in one change — a record's {@code toString} published as a
 * document's subject, and a cast that would have survived compiling with an element inserted ahead
 * of it — and nothing but a reader caught either.
 *
 * <p>Nothing here is a projection made for a reader. Where a measure already holds the item — a
 * point of a border, a question nothing answered, an arm — that value arrives whole, because a value
 * taken apart at a seam loses a part at every one it crosses and a value that is not taken apart
 * cannot lose one. Words about these belong to whoever writes a sentence: a report can name a file
 * and a diagnostic cannot, and the two are readings of one item rather than one of them being handed
 * the other's answer.
 *
 * <p>Which {@link Adequacy.Kind} a finding has is derived from this and is not held beside it, so a
 * kind and what it is about cannot disagree. This does not know its own kind: the classification and
 * the word a document publishes for it are downstream of what the finding is about, and a subject
 * that answered which public category it lands in would be the leak this type exists to close.
 *
 * <p>Every one of these holds what it names. A finding whose subject is absent is a finding about
 * nothing, and the reader that would find out is whichever surface first asks the subject a
 * question — a different one per surface, and none of them where the finding was made. The list
 * this replaced refused a null element as a side effect of being copied, and a shape that says so
 * itself keeps what the copy was doing by accident.
 */
public sealed interface About {

    /** A case of the output no row expects. */
    record ACaseNoRowExpects(TypeSymbol missing) implements About {
        public ACaseNoRowExpects {
            java.util.Objects.requireNonNull(missing, "a finding is about something");
        }
    }

    /** A case some row expects and nothing was seen to produce. */
    record ACaseNothingWasSeenToProduce(TypeSymbol missing) implements About {
        public ACaseNothingWasSeenToProduce {
            java.util.Objects.requireNonNull(missing, "a finding is about something");
        }
    }

    /** A case of an input no row applies the behavior to. The evidence names which input, so that a
     *  case and the position it is a case of arrive together. */
    record ACaseNoRowAppliesItTo(InputCaseEvidence input, TypeSymbol missing) implements About {
        public ACaseNoRowAppliesItTo {
            java.util.Objects.requireNonNull(input, "a finding is about something");
            java.util.Objects.requireNonNull(missing, "a finding is about something");
        }
    }

    /** A class of a derived position no row is in, which knows the position it is a class of. */
    record AClassNoRowIsIn(PartitionEvidence.AxisClass axisClass) implements About {
        public AClassNoRowIsIn {
            java.util.Objects.requireNonNull(axisClass, "a finding is about something");
        }
    }

    /**
     * A point of a border no row is at.
     *
     * <p>The assessment's own item, which is what the count, the document and this are three
     * readings of. Held as the point rather than as the axis, the value, the rule and the role,
     * which is what those four fields were: a copy that did not identify a point, since several
     * rules can draw a line at one value.
     *
     * <p>What is here is what was measured, and a reader wanting more than that says so. A
     * generation composes values at these lines whatever the build was measuring, so what it can do
     * about a finding is read out of the search it asked for — the same point of the same line,
     * found with the line itself ({@link BorderAssessment#owedAt}). This carries the measurement
     * because that is what a finding is about: a search settles what can be written at the point and
     * changes nothing about the point being missed.
     */
    record APointOfABorder(BorderAssessment.Point point) implements About {
        public APointOfABorder {
            java.util.Objects.requireNonNull(point, "a finding is about something");
        }
    }

    /**
     * A finding about one rule of the model, which is what carries its identity.
     *
     * <p>Which findings these are is answered here and nowhere else. Read off a list of kinds, a
     * writer had to be told again every time one was added â and a kind added and not told wrote no
     * identity, which is one rule's findings coming out identical in every field with nothing to
     * join them by. A shape that is about a rule says so by being one of these.
     */
    sealed interface OfARule extends About {

        /** Which rule, as everything that names a rule names it. */
        souther.compiler.check.RuleRef rule();
    }

    /**
     * A finding the document writes as {@code partition_not_read}, whichever authority answered.
     *
     * <p>Both shapes carry a limit, and a reader acts on it: which one is in the way is the thing
     * either finding was added to say. Asked here rather than matched against the kinds that have
     * one, for the reason {@link OfARule} is: a shape added and not listed writes no limit, and one
     * rule's findings at one position come out identical wherever it stopped for two of them.
     *
     * <p>Named after the kind these are written under, and it is wider than its own word — a rule
     * read from end to end that draws no line is one of them. Which is a decision about the
     * schema's vocabulary rather than about this grouping, and it is written down beside
     * {@link PartitionEvidence.NotRead}, where the document's shape is.
     */
    sealed interface OfSomethingNotRead extends About {

        /** The finding itself, whose reason is what a document promises its reader. */
        PartitionEvidence.NotRead finding();
    }

    /** A position the model draws no line through. */
    record APositionNoLineDivides(
            souther.compiler.partition.UndividedPosition position) implements About {
        public APositionNoLineDivides {
            java.util.Objects.requireNonNull(position, "a finding is about something");
        }
    }

    /**
     * A rule of the model this read and could not turn into a line, and what stopped it.
     *
     * <p>Named by the rule, because a position is not what an author edits. Carrying only the
     * position, the sentence written from this told an author that a rule about somewhere went
     * unread and left them to work out which rule — which the accounting was made to say and this
     * measure beside it was not.
     */
    record ARuleWithoutALine(PartitionEvidence.NotRead.ARule finding)
            implements OfARule, OfSomethingNotRead {
        public ARuleWithoutALine {
            java.util.Objects.requireNonNull(finding, "a finding is about something");
        }

        @Override
        public souther.compiler.check.RuleRef rule() {
            return finding.rule();
        }
    }

    /**
     * A position whose rules this reading never arrived at, with what stopped it.
     *
     * <p>Its own shape beside the rule above, and not that one with the rule left out. There is no
     * rule to name here and a reader is owed the position and the limit; a consumer told to read an
     * absent field to know which of the two it holds is reconstructing the authority from the
     * payload.
     */
    record APositionThisCouldNotRead(PartitionEvidence.NotRead.APosition finding)
            implements OfSomethingNotRead {
        public APositionThisCouldNotRead {
            java.util.Objects.requireNonNull(finding, "a finding is about something");
        }
    }

    /**
     * A position whose values are read from a product this reading cannot show the rules admit.
     *
     * <p>Beside the two above and not among them. Every rule about the position arrived and every
     * one was taken in, so there is no rule to name and nothing was left unreached — what a reader
     * is owed is that the classes may hold one no value can be in, and that what would lift it is a
     * reading that keeps the alternatives apart.
     */
    record APositionReadWiderThanItsRules(
            souther.compiler.inputs.PositionValuesNotSeparated finding) implements About {
        public APositionReadWiderThanItsRules {
            java.util.Objects.requireNonNull(finding, "a finding is about something");
        }
    }

    /** A position the axes measure whose rules the walk never reached. */
    record APositionWhoseRulesWereNotReached(
            PartitionEvidence.AxisCoverage axis) implements About {
        public APositionWhoseRulesWereNotReached {
            java.util.Objects.requireNonNull(axis, "a finding is about something");
        }
    }

    /**
     * A question a rule raised that nothing answered.
     *
     * <p>The accounting's own value, whose own contract is that it is handed on whole rather than
     * taken apart. It was taken apart into six elements one seam later, which is the thing that
     * contract was written against.
     */
    record AQuestionNothingAnswered(PartitionEvidence.Unanswered asked) implements OfARule {

        @Override
        public souther.compiler.check.RuleRef rule() {
            return asked.rule();
        }

        public AQuestionNothingAnswered {
            java.util.Objects.requireNonNull(asked, "a finding is about something");
        }
    }

    /** An arm of the body no row goes through. */
    record AnArmNoRowGoesThrough(
            souther.compiler.coverage.CoverageSites.Site arm) implements About {
        public AnArmNoRowGoesThrough {
            java.util.Objects.requireNonNull(arm, "a finding is about something");
        }
    }
}
