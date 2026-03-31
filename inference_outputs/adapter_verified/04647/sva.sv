module subtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);

// Y equals A - B on each sampled cycle.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (A - B)
    );

// When B is zero, Y equals A.
    check_zero_subtrahend: assert property (
        @(posedge clk) (B == 4'h0) |-> (Y == A)
    );

// When A equals B, Y is zero.
    check_equal_operands_zero: assert property (
        @(posedge clk) (A == B) |-> (Y == 4'h0)
    );

// Subtracting 1 from 0 yields 15 (4-bit wrap).
    check_wrap_from_zero: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h1)) |-> (Y == 4'hF)
    );

// Subtracting 1 from 1 yields 0.
    check_wrap_from_one: assert property (
        @(posedge clk) ((A == 4'h1) && (B == 4'h1)) |-> (Y == 4'h0)
    );

// Subtracting 1 from 2 yields 1.
    check_wrap_from_two: assert property (
        @(posedge clk) ((A == 4'h2) && (B == 4'h1)) |-> (Y == 4'h1)
    );

// Subtracting 1 from 3 yields 2.
    check_wrap_from_three: assert property (
        @(posedge clk) ((A == 4'h3) && (B == 4'h1)) |-> (Y == 4'h2)
    );

// Subtracting 1 from 4 yields 3.
    check_wrap_from_four: assert property (
        @(posedge clk) ((A == 4'h4) && (B == 4'h1)) |-> (Y == 4'h3)
    );

// Subtracting 1 from 5 yields 4.
    check_wrap_from_five: assert property (
        @(posedge clk) ((A == 4'h5) && (B == 4'h1)) |-> (Y == 4'h4)
    );

// Subtracting 1 from 6 yields 5.
    check_wrap_from_six: assert property (
        @(posedge clk) ((A == 4'h6) && (B == 4'h1)) |-> (Y == 4'h5)
    );

// Subtracting 1 from 7 yields 6.
    check_wrap_from_seven: assert property (
        @(posedge clk) ((A == 4'h7) && (B == 4'h1)) |-> (Y == 4'h6)
    );

// Subtracting 1 from 8 yields 7.
    check_wrap_from_eight: assert property (
        @(posedge clk) ((A == 4'h8) && (B == 4'h1)) |-> (Y == 4'h7)
    );

// Subtracting 1 from 9 yields 8.
    check_wrap_from_nine: assert property (
        @(posedge clk) ((A == 4'h9) && (B == 4'h1)) |-> (Y == 4'h8)
    );

// Subtracting 1 from 10 yields 9.
    check_wrap_from_ten: assert property (
        @(posedge clk) ((A == 4'hA) && (B == 4'h1)) |-> (Y == 4'h9)
    );

// Subtracting 1 from 11 yields 10.
    check_wrap_from_eleven: assert property (
        @(posedge clk) ((A == 4'hB) && (B == 4'h1)) |-> (Y == 4'hA)
    );

// Subtracting 1 from 12 yields 11.
    check_wrap_from_twelve: assert property (
        @(posedge clk) ((A == 4'hC) && (B == 4'h1)) |-> (Y == 4'hB)
    );

// Subtracting 1 from 13 yields 12.
    check_wrap_from_thirteen: assert property (
        @(posedge clk) ((A == 4'hD) && (B == 4'h1)) |-> (Y == 4'hC)
    );

// Subtracting 1 from 14 yields 13.
    check_wrap_from_fourteen: assert property (
        @(posedge clk) ((A == 4'hE) && (B == 4'h1)) |-> (Y == 4'hD)
    );

// Subtracting 1 from 15 yields 14.
    check_wrap_from_fifteen: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'h1)) |-> (Y == 4'hE)
    );

endmodule
