module xor_gate_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out_case
);

    ///// Functional correctness /////
    // Out should equal XOR of previous-cycle inputs.
    check_out_is_prev_xor: assert property (
        @(posedge clk) $past(1'b1) |-> (out_case == ($past(a) ^ $past(b)))
    );

    // If previous inputs were 00, out must be 0.
    check_truth_00: assert property (
        @(posedge clk) $past(1'b1) && ($past({a,b}) == 2'b00) |-> (out_case == 1'b0)
    );

    // If previous inputs were 01, out must be 1.
    check_truth_01: assert property (
        @(posedge clk) $past(1'b1) && ($past({a,b}) == 2'b01) |-> (out_case == 1'b1)
    );

    // If previous inputs were 10, out must be 1.
    check_truth_10: assert property (
        @(posedge clk) $past(1'b1) && ($past({a,b}) == 2'b10) |-> (out_case == 1'b1)
    );

    // If previous inputs were 11, out must be 0.
    check_truth_11: assert property (
        @(posedge clk) $past(1'b1) && ($past({a,b}) == 2'b11) |-> (out_case == 1'b0)
    );

endmodule