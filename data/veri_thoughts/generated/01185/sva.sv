module xor_gate_sva (
    input logic a,
    input logic b,
    input logic out
);
    // Output equals XOR of inputs on any input edge.
    check_xor_function: assert property (
        @(posedge a or negedge a or posedge b or negedge b) out == (a ^ b)
    );

    // 00 -> out is 0.
    check_truth_00: assert property (
        @(posedge a or negedge a or posedge b or negedge b) ((a == 1'b0) && (b == 1'b0)) |-> (out == 1'b0)
    );

    // 01 -> out is 1.
    check_truth_01: assert property (
        @(posedge a or negedge a or posedge b or negedge b) ((a == 1'b0) && (b == 1'b1)) |-> (out == 1'b1)
    );

    // 10 -> out is 1.
    check_truth_10: assert property (
        @(posedge a or negedge a or posedge b or negedge b) ((a == 1'b1) && (b == 1'b0)) |-> (out == 1'b1)
    );

    // 11 -> out is 0.
    check_truth_11: assert property (
        @(posedge a or negedge a or posedge b or negedge b) ((a == 1'b1) && (b == 1'b1)) |-> (out == 1'b0)
    );

    // Rising edge on out implies inputs differ.
    check_out_rise_matches_inputs: assert property (
        @(posedge out) (a ^ b) == 1'b1
    );

    // Falling edge on out implies inputs are equal.
    check_out_fall_matches_inputs: assert property (
        @(negedge out) (a ^ b) == 1'b0
    );
endmodule