module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

// Sum must equal the 5-bit addition of A, B, and Cin.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

// S must match the lower 4 bits of the addition result.
    check_sum_bits: assert property (
        @(posedge clk) S == ({1'b0, A} + {1'b0, B} + Cin)[3:0]
    );

// Cout must match the carry-out bit of the addition result.
    check_cout_bit: assert property (
        @(posedge clk) Cout == ({1'b0, A} + {1'b0, B} + Cin)[4]
    );

// Zero inputs must produce a zero sum and no carry.
    check_zero_case: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Cin == 1'b0) |-> (S == 4'h0 && Cout == 1'b0)
    );

// Adding zero with no carry-in must pass A through unchanged.
    check_a_passthrough: assert property (
        @(posedge clk) (B == 4'h0 && Cin == 1'b0) |-> (S == A && Cout == 1'b0)
    );

// Adding zero with no carry-in must pass B through unchanged.
    check_b_passthrough: assert property (
        @(posedge clk) (A == 4'h0 && Cin == 1'b0) |-> (S == B && Cout == 1'b0)
    );

// Maximum inputs must produce 4'hF with carry-out asserted.
    check_max_case: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> (S == 4'hF && Cout == 1'b1)
    );

endmodule
