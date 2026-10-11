package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
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
                souther.compiler.check.ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
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
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseMovedDateParts.class,
                builderOf(part("year", aDayBack()), part("month", ValueTransformation.NONE)));
    }

    @Test
    void aMovedYearBesideAMonthAndADayOfTheDateItselfIsOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseMovedDateParts.class,
                builderOf(part("year", aDayBack()), part("month", ValueTransformation.NONE),
                        part("day", ValueTransformation.NONE)));
    }

    @Test
    void aMovedYearBesideTheYearOfTheDateItselfIsOneDate() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseMovedDateParts.class,
                builderOf(part("year", aDayBack()), part("year", ValueTransformation.NONE)));
    }

    @Test
    void thePartsOfADateThatIsNotMovedAreStillSpelledInParts() {
        assertInstanceOf(TermRealizations.JointBuilder.OnThoseDateParts.class,
                builderOf(part("year", ValueTransformation.NONE),
                        part("month", ValueTransformation.NONE)));
    }
}
