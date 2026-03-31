module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

// Sum equals 4-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) S == (A + B)
    );

// Carry-out equals overflow of 4-bit addition.
    check_cout_matches_overflow: assert property (
        @(posedge clk) Cout == ((A + B) > 4'hF)
    );

// When no overflow, sum is 4 bits and carry is 0.
    check_no_overflow_result: assert property (
        @(posedge clk) ((A + B) <= 4'hF) |-> (S[3:0] == (A + B)) && (Cout == 1'b0)
    );

// When overflow, sum is truncated and carry is 1.
    check_overflow_result: assert property (
        @(posedge clk) ((A + B) > 4'hF) |-> (S[3:0] == (A + B)) && (Cout == 1'b1)
    );

// Maximum inputs produce 4'hF with carry asserted.
    check_max_inputs: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF) |-> (S == 4'hF) && (Cout == 1'b1)
    );

// Zero on B passes A through with no carry.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> (S == A) && (Cout == 1'b0)
    );

// Zero on A passes B through with no carry.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> (S == B) && (Cout == 1'b0)
    );

endmodule
