module adder4_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

// Sum output matches the 4-bit addition of A, B, and CIN.
    check_sum_matches_addition: assert property (
        @(posedge clk) S == (A + B + CIN)
    );

// COUT matches the carry-out bit of the 4-bit addition.
    check_cout_matches_carry: assert property (
        @(posedge clk) COUT == ((A + B + CIN) >= 5'd16)
    );

// Zero inputs produce a zero sum and no carry.
    check_zero_inputs: assert property (
        @(posedge clk) (A == 4'd0 && B == 4'd0 && CIN == 1'b0) |-> (S == 4'd0 && COUT == 1'b0)
    );

// Maximum inputs produce 4'hF with carry-out asserted.
    check_max_inputs: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> (S == 4'hF && COUT == 1'b1)
    );

// Adding zero with no carry-in passes A through unchanged.
    check_a_passthrough_when_b_zero: assert property (
        @(posedge clk) (B == 4'd0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

// Adding zero with no carry-in passes B through unchanged.
    check_b_passthrough_when_a_zero: assert property (
        @(posedge clk) (A == 4'd0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

// A carry-in increments 4'hF to 4'h0 with carry-out asserted.
    check_cin_increments_max: assert property (
        @(posedge clk) (A == 4'hF && B == 4'd0 && CIN == 1'b1) |-> (S == 4'h0 && COUT == 1'b1)
    );

// A carry-in increments 4'hF with B==1 to 4'h1 with carry-out asserted.
    check_cin_with_b_one: assert property (
        @(posedge clk) (A == 4'hF && B == 4'd1 && CIN == 1'b1) |-> (S == 4'h1 && COUT == 1'b1)
    );

endmodule
