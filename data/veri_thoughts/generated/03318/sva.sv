module flip_flop_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic RESET_B
);

    // A sampled active-low reset must leave Q low at the next clock sample.
    check_reset_forces_q_low: assert property (
        @(posedge CLK)
        !RESET_B |=> (Q == 1'b0)
    );

    // With reset inactive, SCE forces Q low whenever SCD is low.
    check_sce_forces_q_low: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!SCD && SCE) |=> (Q == 1'b0)
    );

    // With reset inactive and both controls low, D=0 is captured into Q.
    check_d_zero_captured: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!SCD && !SCE && !D) |=> (Q == 1'b0)
    );

    // Q can rise only from the SCD path or from capturing D=1 with both controls low.
    check_q_rise_has_valid_source: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        $rose(Q) |-> ($past(SCD) || (!$past(SCD) && !$past(SCE) && $past(D)))
    );

endmodule