module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       SUB,
    input logic [3:0] out
);

    // In add mode, out must be the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock) (SUB == 1'b0) |-> (out == (A + B))
    );

    // In subtract mode, out must be the 4-bit difference of A and B.
    check_sub_mode_result: assert property (
        @($global_clock) (SUB == 1'b1) |-> (out == (A - B))
    );

    // If all inputs stay the same, the combinational output must stay the same.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) !$initstate && $stable({A, B, SUB}) |-> $stable(out)
    );

endmodule