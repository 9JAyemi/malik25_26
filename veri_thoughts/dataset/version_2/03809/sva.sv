module adder_subtractor_4bit_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] result,
    input logic OVFL
);

    // In add mode, result is the 4-bit sum of A and B.
    check_add_result: assert property (
        @(posedge clk) !SUB |-> (result == (A + B))
    );

    // In subtract mode, result is the 4-bit difference of A and B.
    check_sub_result: assert property (
        @(posedge clk) SUB |-> (result == (A - B))
    );

    // OVFL always matches the MSB of result.
    check_ovfl_matches_result_msb: assert property (
        @(posedge clk) OVFL == result[3]
    );

    // The outputs match the selected arithmetic operation every cycle.
    check_selected_operation: assert property (
        @(posedge clk) result == (SUB ? (A - B) : (A + B))
    );

    // Stable inputs keep the combinational outputs stable across samples.
    check_stable_inputs_hold_outputs: assert property (
        @(posedge clk) $stable({A, B, SUB}) |-> $stable({result, OVFL})
    );

endmodule