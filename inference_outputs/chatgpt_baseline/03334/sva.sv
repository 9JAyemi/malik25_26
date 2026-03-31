module four_bit_adder_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Clock,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum registers the previous cycle's 4-bit addition of A, B, and Cin.
    check_sum_matches_previous_add: assert property (
        @(posedge Clock) 1'b1 |=> (Sum == ($past(A) + $past(B) + $past(Cin)))
    );

    // Cout is always low because the RTL adds with 4-bit expression width.
    check_cout_is_zero: assert property (
        @(posedge Clock) 1'b1 |=> (Cout == 1'b0)
    );

    // An overflowing add wraps in Sum and does not raise Cout.
    check_overflow_wraps_without_carry: assert property (
        @(posedge Clock) (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> (Sum == 4'hF && Cout == 1'b0)
    );

endmodule