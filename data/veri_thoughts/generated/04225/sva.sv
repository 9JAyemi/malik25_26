module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    // The 5-bit output matches the zero-extended sum of A and B.
    check_full_sum_correct: assert property (
        @(posedge clk) disable iff (1'b0)
        ({Cout, S} == ({1'b0, A} + {1'b0, B}))
    );

    // Zero plus zero produces a zero result with no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'h0) && (B == 4'h0)) |-> ({Cout, S} == 5'h00)
    );

    // Adding zero on A passes B directly to the output.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'h0) |-> ({Cout, S} == {1'b0, B})
    );

    // Adding zero on B passes A directly to the output.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (B == 4'h0) |-> ({Cout, S} == {1'b0, A})
    );

    // Maximum inputs produce 30 with carry-out asserted.
    check_max_plus_max: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'hf) && (B == 4'hf)) |-> ({Cout, S} == 5'h1e)
    );

endmodule