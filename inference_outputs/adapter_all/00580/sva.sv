module binary_subtractor_32bit_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S
);

    // S must equal A minus B.
    check_subtract_result: assert property (
        @(posedge clk) S == (A - B)
    );

    // Subtracting zero on B must pass A through unchanged.
    check_zero_subtrahend: assert property (
        @(posedge clk) (B == 32'h0000_0000) |-> (S == A)
    );

    // Subtracting zero on A must produce zero.
    check_zero_minuend: assert property (
        @(posedge clk) (A == 32'h0000_0000) |-> (S == 32'h0000_0000)
    );

    // Subtracting equal operands must produce zero.
    check_equal_operands: assert property (
        @(posedge clk) (A == B) |-> (S == 32'h0000_0000)
    );

    // Subtracting one from zero must produce all ones.
    check_one_minus_zero: assert property (
        @(posedge clk) ((A == 32'h0000_0000) && (B == 32'h0000_0001)) |-> (S == 32'hFFFF_FFFF)
    );

    // Subtracting all ones from zero must produce one.
    check_all_ones_minus_zero: assert property (
        @(posedge clk) ((A == 32'h0000_0000) && (B == 32'hFFFF_FFFF)) |-> (S == 32'h0000_0001)
    );

    // Subtracting zero from all ones must produce all ones.
    check_all_ones_minus_zero: assert property (
        @(posedge clk) ((A == 32'hFFFF_FFFF) && (B == 32'h0000_0000)) |-> (S == 32'hFFFF_FFFF)
    );

    // Subtracting one from all ones must produce zero.
    check_all_ones_minus_one: assert property (
        @(posedge clk) ((A == 32'hFFFF_FFFF) && (B == 32'h0000_0001)) |-> (S == 32'h0000_0000)
    );

    // Subtracting 0x8000_0000 from itself must produce zero.
    check_self_subtraction_80000000: assert property (
        @(posedge clk) ((A == 32'h8000_0000) && (B == 32'h8000_0000)) |-> (S == 32'h0000_0000)
    );

    // Subtracting 0x7FFFFFFF from itself must produce zero.
    check_self_subtraction_7FFFFFFF: assert property (
        @(posedge clk) ((A == 32'h7FFFFFFF) && (B == 32'h7FFFFFFF)) |-> (S == 32'h0000_0000)
    );

endmodule