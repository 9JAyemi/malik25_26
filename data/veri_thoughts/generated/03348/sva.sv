module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       clk,
    input logic [3:0] S,
    input logic       Cout
);

    // Outputs must register the previous cycle's 5-bit addition.
    check_registered_addition: assert property (
        @(posedge clk)
        1'b1 |=> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)))
    );

    // Overflow in the current cycle must set carry on the next cycle.
    check_overflow_sets_carry: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) > 5'd15) |=> (Cout == 1'b1)
    );

    // No overflow in the current cycle must clear carry on the next cycle.
    check_no_overflow_clears_carry: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |=> (Cout == 1'b0)
    );

    // Zero inputs must produce zero outputs on the next cycle.
    check_zero_case: assert property (
        @(posedge clk)
        (A == 4'd0 && B == 4'd0 && Cin == 1'b0) |=> (S == 4'd0 && Cout == 1'b0)
    );

    // A sum of 15 must produce 0xF with no carry on the next cycle.
    check_boundary_fifteen: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) == 5'd15) |=> (S == 4'hF && Cout == 1'b0)
    );

    // A sum of 16 must wrap to 0 with carry on the next cycle.
    check_boundary_sixteen: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) == 5'd16) |=> (S == 4'd0 && Cout == 1'b1)
    );

    // Maximum inputs must produce 0xF with carry on the next cycle.
    check_max_input_case: assert property (
        @(posedge clk)
        (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> (S == 4'hF && Cout == 1'b1)
    );

endmodule