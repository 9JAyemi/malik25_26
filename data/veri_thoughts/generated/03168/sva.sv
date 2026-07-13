module dff_rps_sva (
    input logic Q,
    input logic Qbar,
    input logic D,
    input logic R,
    input logic S,
    input logic CLK
);

    // Synchronous reset forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        R |=> (Q == 1'b0)
    );

    // Reset has priority over preset when both are high.
    check_reset_priority_over_preset: assert property (
        @(posedge CLK) disable iff (1'b0)
        (R && S) |=> (Q == 1'b0)
    );

    // Preset forces Q high when reset is low.
    check_preset_forces_q_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!R && S) |=> (Q == 1'b1)
    );

    // With reset and preset low, D=1 is captured into Q.
    check_data_capture_one: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!R && !S && D) |=> (Q == 1'b1)
    );

    // With reset and preset low, D=0 is captured into Q.
    check_data_capture_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!R && !S && !D) |=> (Q == 1'b0)
    );

    // Qbar is always the complement of Q.
    check_qbar_is_complement: assert property (
        @(posedge CLK) disable iff (1'b0)
        (Qbar == ~Q)
    );

endmodule