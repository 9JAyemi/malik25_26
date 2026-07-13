module d_ff_set_clear_sva (
    input logic D,
    input logic CLK,
    input logic SET_B,
    input logic SCD,
    input logic Q
);
    // Q next-cycle equals priority mux of inputs sampled this cycle.
    check_next_q_matches_priority_mux: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ((SET_B == 1'b0) ? 1'b1 : ((SCD == 1'b0) ? 1'b0 : D)))
    );

    // Active-low SET_B forces Q to 1 on the next cycle.
    check_set_forces_one: assert property (
        @(posedge CLK) (SET_B == 1'b0) |=> (Q == 1'b1)
    );

    // Active-low SCD forces Q to 0 on the next cycle when SET_B is not active.
    check_clear_forces_zero: assert property (
        @(posedge CLK) (SET_B != 1'b0 && SCD == 1'b0) |=> (Q == 1'b0)
    );

    // With no set/clear active, Q captures D on the next cycle.
    check_data_captured: assert property (
        @(posedge CLK) (SET_B != 1'b0 && SCD != 1'b0) |=> (Q == D)
    );

    // When both SET_B and SCD are low, set has priority and Q becomes 1.
    check_set_overrides_clear: assert property (
        @(posedge CLK) (SET_B == 1'b0 && SCD == 1'b0) |=> (Q == 1'b1)
    );
endmodule