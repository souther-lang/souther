package souther.compiler.partition;

import souther.compiler.check.PathReachability;
import souther.compiler.reading.CoverageRead;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a behavior's body reads of its input: how far it tells each position's classes apart, and
 * which classes of two positions a run reads together.
 *
 * <p>One reading of the ways and two answers off it. Read apart, the ways would be walked twice and
 * the two answers could disagree about what a way is — which way a decision is on is what both
 * of them turn on.
 *
 * @param distinctions what the body tells apart at each position
 * @param together     which classes of two positions a run reads together
 */
public record BodyInputReading(Map<AxisId, BodyDistinction> distinctions,
                               ReadTogether together) {

    public BodyInputReading {
        distinctions = Map.copyOf(distinctions);
    }

    /** What a behavior with no body reads at each of {@code axes}, which is unknown. */
    public static BodyInputReading withoutABody(List<Axis> axes) {
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            out.put(axis.id(), new BodyDistinction.NoBody());
        }
        return new BodyInputReading(out, new ReadTogether.Every());
    }

    /**
     * What the body read as {@code read} reads at each position {@code subject} measures, with what
     * the reading of the input found about the rules it drew no line for.
     *
     * <p>Read off the ways runs take and nothing else ({@link CoverageRead.Read#taken}). Taken from
     * the ways in to the arms or the meetings as well, a way no run takes would be read as a
     * decision the body makes.
     *
     * <p>And with the case each arm of a {@code match} is where the tree that runs could not name
     * it ({@link ArmsNamed}): such an arm, on what a closure was handed, is one application and
     * takes its element's case. And with which positions a fork it could name no subject for may
     * turn on ({@link ForkDependencies}), which is what such a fork leaves unread and all it does.
     *
     * <p>A way through a place {@code arrives} proves nothing reaches is a way no run takes. The
     * reading of the runs keeps every way it could not rule out itself, and what the model's rules
     * prove of the places on it is the other half of whether a run takes it — the half the
     * obligations and the dead branches are read off as well.
     */
    public static BodyInputReading of(CoverageRead.Read read, MeasuredInput subject,
                                      PathReachability.Answers arrives) {
        return WhatABodyTellsApart.of(read, subject.axes(),
                subject.partitioning().rulesWithoutALine(),
                subject.partitioning().armsNamed(), subject.partitioning().dependencies(),
                arrives);
    }
}
