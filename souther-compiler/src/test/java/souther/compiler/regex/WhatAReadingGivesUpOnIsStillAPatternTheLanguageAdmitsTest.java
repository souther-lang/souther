package souther.compiler.regex;

import org.junit.jupiter.api.Test;
import net.unit8.notation199x.pattern.PatternRead;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every budget a reading of the rules is given stops short of the states a pattern may come to.
 *
 * <p>A reading past its budget leaves the question unanswered and the program standing, so between
 * the two there has to be room for a pattern the reading gave up on and the reader admitted. What a
 * machine costs to build is 199x-notation's to bound and to test; the budgets are this compiler's,
 * and where they stand against the reader's limit is asked here.
 */
class WhatAReadingGivesUpOnIsStillAPatternTheLanguageAdmitsTest {

    /**
     * Asked of every budget declared, so one added later is held to it without being listed here,
     * and of the limit as the reader holds it, so a reader that lowered it is caught.
     */
    @Test
    void whatAReadingGivesUpOnIsStillAPatternTheLanguageAdmits() throws IllegalAccessException {
        List<String> reaching = new ArrayList<>();
        int readings = 0;
        for (Field field : PatternPlan.Budget.class.getFields()) {
            if (!Modifier.isStatic(field.getModifiers()) || field.getType() != PatternPlan.Budget.class) {
                continue;
            }
            readings++;
            PatternPlan.Budget reading = (PatternPlan.Budget) field.get(null);
            if (reading.mostStates() >= PatternRead.Limit.MACHINE_STATES.most()) {
                reaching.add(field.getName());
            }
        }
        assertEquals(List.of(), reaching);
        assertTrue(readings > 1, "the walk found the readings' budgets: " + readings);
    }
}
