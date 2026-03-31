module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Clock,
    input logic [3:0] Sum,
    input logic Cout
);

// Sum is the 4-bit result of A + B + Cin from the previous cycle.
    check_sum_registered: assert property (
        @(posedge Clock) 1'b1 |=> (Sum == ($past(A) + $past(B) + $past(Cin)))
    );

// Cout is the carry-out from the previous cycle's addition.
    check_cout_registered: assert property (
        @(posedge Clock) 1'b1 |=> (Cout == (({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)) >= 5'd16))
    );

// Zero inputs produce zero outputs on the next cycle.
    check_zero_case: assert property (
        @(posedge Clock) (A == 4'h0 && B == 4'h0 && Cin == 1'b0) |=> (Sum == 4'h0 && Cout == 1'b0)
    );

// Maximum inputs produce 4'hF and carry-out on the next cycle.
    check_max_case: assert property (
        @(posedge Clock) (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> (Sum == 4'hF && Cout == 1'b1)
    );

endmodule
