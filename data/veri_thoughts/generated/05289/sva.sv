module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] C,
    input logic       Cout
);

    // Outputs equal the prior cycle's registered 5-bit sum.
    check_registered_sum: assert property (
        @(posedge clk)
        1'b1 |=> ({Cout, C} == $past({1'b0, A} + {1'b0, B} + {4'b0, Cin}))
    );

    // No overflow in the current inputs implies Cout is low next cycle.
    check_cout_low_without_overflow: assert property (
        @(posedge clk)
        ({1'b0, A} + {1'b0, B} + {4'b0, Cin} <= 5'd15) |=> (Cout == 1'b0)
    );

    // Overflow in the current inputs implies Cout is high next cycle.
    check_cout_high_with_overflow: assert property (
        @(posedge clk)
        ({1'b0, A} + {1'b0, B} + {4'b0, Cin} > 5'd15) |=> (Cout == 1'b1)
    );

    // With A and B at zero, the next output equals Cin.
    check_cin_only_sum: assert property (
        @(posedge clk)
        (A == 4'h0 && B == 4'h0) |=> ({Cout, C} == {4'b0000, $past(Cin)})
    );

    // With B and Cin at zero, the next output passes A through.
    check_pass_a_when_b_and_cin_zero: assert property (
        @(posedge clk)
        (B == 4'h0 && Cin == 1'b0) |=> ({Cout, C} == {1'b0, $past(A)})
    );

    // With A and Cin at zero, the next output passes B through.
    check_pass_b_when_a_and_cin_zero: assert property (
        @(posedge clk)
        (A == 4'h0 && Cin == 1'b0) |=> ({Cout, C} == {1'b0, $past(B)})
    );

    // Maximum inputs produce the maximum 5-bit result on the next cycle.
    check_max_inputs_max_sum: assert property (
        @(posedge clk)
        (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> ({Cout, C} == 5'h1F)
    );

endmodule