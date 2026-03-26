module func_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the AND function implemented by the RTL.
    check_x_matches_and_of_inputs: assert property (
        @(posedge clk) X === ((A === 1'b1) && (B === 1'b1) && (C === 1'b1))
    );

    // When all inputs are exactly 1, X must be 1.
    check_x_high_when_all_inputs_high: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1)) |-> (X === 1'b1)
    );

    // If any input is not exactly 1, X must be 0.
    check_x_low_when_any_input_not_high: assert property (
        @(posedge clk) ((A !== 1'b1) || (B !== 1'b1) || (C !== 1'b1)) |-> (X === 1'b0)
    );

endmodule