module sky130_fd_sc_hd__a21o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic and0_out,
    input logic or0_out_X
);
    // X equals (A1 & A2) | B1.
    check_function_truth: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        X == ((A1 & A2) | B1)
    );

    // and0_out equals A1 & A2.
    check_internal_and_gate: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        and0_out == (A1 & A2)
    );

    // or0_out_X equals and0_out | B1.
    check_internal_or_gate: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        or0_out_X == (and0_out | B1)
    );

    // X equals or0_out_X through the buffer.
    check_buf_output: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        X == or0_out_X
    );

    // If B1 is HIGH, X must be HIGH.
    check_b1_forces_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        B1 |-> (X == 1'b1)
    );

    // If A1 and A2 are both HIGH, X must be HIGH.
    check_and_inputs_force_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (A1 & A2) |-> (X == 1'b1)
    );

    // If all inputs are LOW, X must be LOW.
    check_all_low_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (!A1 && !A2 && !B1) |-> (X == 1'b0)
    );

    // When B1 is LOW, X equals A1 & A2.
    check_b1_low_x_equals_and: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (B1 == 1'b0) |-> (X == (A1 & A2))
    );

    // When A1 & A2 is 0, X equals B1.
    check_and_zero_x_equals_b1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        ((A1 & A2) == 1'b0) |-> (X == B1)
    );

    // If X is HIGH, either B1 is HIGH or both A1 and A2 are HIGH.
    check_x_high_requires_sources: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (X == 1'b1) |-> (B1 || (A1 & A2))
    );
endmodule