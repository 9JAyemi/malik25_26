module d_ff_set_sva (
    input logic D,
    input logic SET_B,
    input logic CLK,
    input logic Q
);

    // Sequential logic on posedge CLK; no reset is present in the RTL.

    // When SET_B is high at a clock edge, Q is set to 1 on the next cycle.
    check_sync_set_forces_one: assert property (
        @(posedge CLK) SET_B |=> (Q == 1'b1)
    );

    // When SET_B is low and D is 0, Q captures 0 on the next cycle.
    check_capture_zero_when_set_low: assert property (
        @(posedge CLK) (!SET_B && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // When SET_B is low and D is 1, Q captures 1 on the next cycle.
    check_capture_one_when_set_low: assert property (
        @(posedge CLK) (!SET_B && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // Q follows the RTL next-state equation from the prior sampled inputs.
    check_next_state_equation: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ($past(SET_B) ? 1'b1 : $past(D)))
    );

endmodule