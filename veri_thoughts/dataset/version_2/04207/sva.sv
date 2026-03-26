module pulse_generator_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // A sampled rising edge on d produces q high on the next cycle.
    check_q_on_sampled_rise: assert property (
        @(posedge clk) $rose(d) |=> q
    );

    // Without a sampled rising edge on d, q is low on the next cycle.
    check_q_without_sampled_rise: assert property (
        @(posedge clk) (!d || $past(d)) |=> !q
    );

    // If d is low at a clock edge, q is low on the next cycle.
    check_q_low_when_d_low: assert property (
        @(posedge clk) !d |=> !q
    );

    // If d stays high across sampled cycles, q is low on the next cycle.
    check_q_low_when_d_stays_high: assert property (
        @(posedge clk) (d && $past(d)) |=> !q
    );

    // A sampled rise on d creates only a single-cycle pulse on q.
    check_q_single_cycle_pulse: assert property (
        @(posedge clk) $rose(d) |=> q ##1 !q
    );

endmodule