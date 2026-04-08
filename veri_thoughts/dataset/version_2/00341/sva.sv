module my_ff_sva (
    input logic D,
    input logic Q,
    input logic SET_B,
    input logic CLK
);

    // High SET_B forces Q low on the following sampled cycle.
    check_set_b_forces_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($past(SET_B) === 1'b1) |-> (Q === 1'b0)
    );

    // With SET_B low, a sampled 1 on D is captured into Q.
    check_capture_one_when_set_b_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (($past(SET_B) === 1'b0) && ($past(D) === 1'b1)) |-> (Q === 1'b1)
    );

    // With SET_B low, a sampled 0 on D is captured into Q.
    check_capture_zero_when_set_b_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (($past(SET_B) === 1'b0) && ($past(D) === 1'b0)) |-> (Q === 1'b0)
    );

endmodule