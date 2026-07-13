module chatgpt_generate_edge_detect_sva (
    input logic clk,
    input logic rst_n,
    input logic A,
    input logic rise,
    input logic down
);
    // During reset, outputs must be LOW.
    reset_outputs_low: assert property (
        @(posedge clk) !rst_n |-> (rise == 1'b0) && (down == 1'b0)
    );

    // Outputs are never both HIGH simultaneously.
    check_mutual_exclusion: assert property (
        @(posedge clk) disable iff (!rst_n) !(rise && down)
    );

    // On A rising edge, raise 'rise' pulse and not 'down'.
    pulse_on_A_rise: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(A) |-> (rise == 1'b1) && (down == 1'b0)
    );

    // On A falling edge, raise 'down' pulse and not 'rise'.
    pulse_on_A_fall: assert property (
        @(posedge clk) disable iff (!rst_n) $fell(A) |-> (rise == 1'b0) && (down == 1'b1)
    );

    // If A is stable across cycles, no pulses are asserted.
    no_pulse_when_A_stable: assert property (
        @(posedge clk) disable iff (!rst_n) ($stable(A) && $past(rst_n)) |-> (rise == 1'b0) && (down == 1'b0)
    );

    // If 'rise' is asserted, A must have risen (excluding first cycle after reset deassert).
    rise_implies_A_rose: assert property (
        @(posedge clk) disable iff (!rst_n) (rise && $past(rst_n)) |-> $rose(A)
    );

    // If 'down' is asserted, A must have fallen (excluding first cycle after reset deassert).
    down_implies_A_fell: assert property (
        @(posedge clk) disable iff (!rst_n) (down && $past(rst_n)) |-> $fell(A)
    );

    // 'rise' is a single-cycle pulse.
    rise_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) rise |=> !rise
    );

    // 'down' is a single-cycle pulse.
    down_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) down |=> !down
    );

    // Exactly one pulse occurs iff A toggles (excluding first cycle after reset deassert).
    pulses_match_toggle: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> ((rise ^ down) == (A ^ $past(A)))
    );

    // On first cycle after reset deassert, 'down' must be 0 and 'rise' equals A.
    first_cycle_after_reset_outputs: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (down == 1'b0) && (rise == A)
    );
endmodule