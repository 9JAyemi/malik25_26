module logic_gates_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);

    // Output matches the AND of the two inputs.
    check_and_equivalence: assert property (
        @(posedge clk) out == (in1 & in2)
    );

    // Both inputs high drive the output high.
    check_both_inputs_high: assert property (
        @(posedge clk) (in1 & in2) |-> out
    );

    // A low in1 forces the output low.
    check_in1_low_forces_out_low: assert property (
        @(posedge clk) !in1 |-> !out
    );

    // A low in2 forces the output low.
    check_in2_low_forces_out_low: assert property (
        @(posedge clk) !in2 |-> !out
    );

    // A high output requires both inputs high.
    check_out_high_requires_both_inputs: assert property (
        @(posedge clk) out |-> (in1 & in2)
    );

endmodule