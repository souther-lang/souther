package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ObservationSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which way of writing one date answers a group of numbers of it turns on what is asked of the
 * date and not on how it is spelled: a year after a move is asked together with the parts of the
 * date as it stands, and none of them leaves the group unsolved because of the others.
 */
class AGroupOfPartsOfOneMovedDateIsWrittenAsOneDateTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final TermPath AT = TermPath.of("b");

    private static RealizationTarget part(String operation, ValueTransformation from) {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(
                ValueName.Stdlib.operation("Date", operation), new ObservationSource(AT, from),
                TakenArguments.NONE, Type.Prim.DATE,
                ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
        assertNotNull(made, operation);
        return RealizationTarget.of(made);
    }

    private static ValueTransformation aDayBack() {
        return ValueTransformation.of(DateTranslation.none().thenAddDays(-1));
    }

    private static TermRealizations.JointBuilder builderOf(RealizationTarget... group) {
        TermRealizations.JointRealization made =
                TermRealizations.jointRealizationOf(List.of(group));
        return assertInstanceOf(TermRealizations.JointRealization.Supported.class, made,
                "the group is one nothing here writes a date for").builder();
    }

    @Test
    void aMovedYearBesideAMonthOfTheDateItselfIsOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("year", aDayBack()), part("month", ValueTransformation.NONE)));
    }

    @Test
    void aMovedYearBesideAMonthAndADayOfTheDateItselfIsOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("year", aDayBack()), part("month", ValueTransformation.NONE),
                        part("day", ValueTransformation.NONE)));
    }

    @Test
    void aMovedYearBesideTheYearOfTheDateItselfIsOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("year", aDayBack()), part("year", ValueTransformation.NONE)));
    }

    /** A moved month and day with no year beside them are one date, looked for over a cycle. */
    @Test
    void aMovedMonthAndDayWithNoYearAreOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("month", aDayBack()), part("day", aDayBack())));
    }

    /** The parts of a date nobody moved are the parts of a date moved by nothing, and are looked
     *  for the same way: there is one way of writing a date for its parts and not two. */
    @Test
    void thePartsOfADateNobodyMovedAreLookedForTheSameWay() {
        TermRealizations.JointBuilder.OnThoseDateParts builder = assertInstanceOf(
                TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("year", ValueTransformation.NONE),
                        part("month", ValueTransformation.NONE)));

        assertTrue(builder.moved().values().stream().allMatch(DateTranslation::isNone),
                builder.moved().toString());
    }
}
