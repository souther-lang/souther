package souther.compiler.report;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.WhyAStopIsNotShown;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.ResourceBundle;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What the report says of an operation whether a run stops in is not resolved, for every reason,
 * holds none of the words that open a finding about a rule: a reader, and every test that sorts the
 * lines of a report by those words, would read the line as that finding. The words said beside a
 * rule are in the sentence only after the rule, so a headline found in one is never its own.
 */
class WhyAStopIsNotResolvedIsSaidInNoFindingsHeadlineTest {

    /** What opens a finding about a rule: the words before {@code : {rule}}. */
    private static final Pattern HEADLINE = Pattern.compile("^([^{:]+): \\{rule\\}");

    @ParameterizedTest
    @ValueSource(strings = {"en", "ja"})
    void noReasonSaysAnotherFindingsHeadline(String language) {
        Locale locale = Locale.forLanguageTag(language);
        List<String> headlines = headlines(locale);
        assertFalse(headlines.isEmpty(), "the findings about a rule are found by their headline");
        Page page = new Page(SourceRendering.namedByIdentity(SourceLayouts.NONE), locale);
        List<String> said = new ArrayList<>();
        for (WhyAStopIsNotShown why : WhyAStopIsNotShown.values()) {
            for (Optional<String> operation : List.of(Optional.of("a + 1"), Optional.<String>empty())) {
                String sentence = page.say(
                        AdequacyReport.stopNotShownSaid(new AStopNotShown(operation, why)));
                for (String headline : headlines) {
                    if (sentence.contains(headline)) {
                        said.add(why + " says `" + headline + "`: " + sentence);
                    }
                }
            }
        }
        assertEquals(List.of(), said);
    }

    private static List<String> headlines(Locale locale) {
        ResourceBundle bundle = ResourceBundle.getBundle("souther.compiler.diag.messages", locale,
                ResourceBundle.Control.getNoFallbackControl(
                        ResourceBundle.Control.FORMAT_PROPERTIES));
        List<String> out = new ArrayList<>();
        for (String key : bundle.keySet().stream().sorted().toList()) {
            Matcher m = HEADLINE.matcher(bundle.getString(key));
            if (key.startsWith("report.") && m.find()) {
                out.add(m.group(1).strip());
            }
        }
        return out;
    }
}
