module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Clock,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum and Cout are the registered 5-bit result of A + B + Cin.
    check_registered_result: assert property (
        @(posedge Clock) 1'b1 |=> ({Cout, Sum} == ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)))
    );

    // Sum is the low 4 bits of the registered result.
    check_sum_matches_result: assert property (
        @(posedge Clock) 1'b1 |=> (Sum == ($past(A) + $past(B) + $past(Cin)))
    );

    // Cout is the carry-out bit of the registered result.
    check_cout_matches_result: assert property (
        @(posedge Clock) 1'b1 |=> (Cout == (({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)) >= 5'd16))
    );

    // Adding zero with no carry-in leaves the inputs unchanged.
    check_zero_addition: assert property (
        @(posedge Clock) (B == 4'h0 && Cin == 1'b0) |=> ({Cout, Sum} == {1'b0, $past(A)})
    );

    // A carry-in increments the zero result by one.
    check_cin_increments_zero: assert property (
        @(posedge Clock) (A == 4'h0 && B == 4'h0 && Cin == 1'b1) |=> ({Cout, Sum} == 5'h01)
    );

    // The maximum input combination produces the maximum 5-bit result.
    check_max_input_case: assert property (
        @(posedge Clock) (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> ({Cout, Sum} == 5'h1F)
    );

endmodule