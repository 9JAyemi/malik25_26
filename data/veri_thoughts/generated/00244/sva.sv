module ripple_carry_adder_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // When bit 0 is 0+0, the upper bits add with carry-in 0.
    check_upper_add_with_zero_lsb_carry: assert property (
        @(posedge clk)
        ((A[0] == 1'b0) && (B[0] == 1'b0)) |->
        ({Cout, Sum[3:1]} === ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

    // When bit 0 is 1+1, the upper bits add with carry-in 1.
    check_upper_add_with_one_lsb_carry: assert property (
        @(posedge clk)
        ((A[0] == 1'b1) && (B[0] == 1'b1)) |->
        ({Cout, Sum[3:1]} === ({1'b0, A[3:1]} + {1'b0, B[3:1]} + 4'b0001))
    );

    // Repeating the same operands repeats the upper outputs when the LSB carry is 0.
    check_repeat_operands_repeat_upper_outputs_zero_carry: assert property (
        @(posedge clk)
        ($past(1'b1, 2) &&
         (A === $past(A, 2)) &&
         (B === $past(B, 2)) &&
         (A[0] == 1'b0) &&
         (B[0] == 1'b0)) |->
        ({Cout, Sum[3:1]} === $past({Cout, Sum[3:1]}, 2))
    );

    // Repeating the same operands repeats the upper outputs when the LSB carry is 1.
    check_repeat_operands_repeat_upper_outputs_one_carry: assert property (
        @(posedge clk)
        ($past(1'b1, 2) &&
         (A === $past(A, 2)) &&
         (B === $past(B, 2)) &&
         (A[0] == 1'b1) &&
         (B[0] == 1'b1)) |->
        ({Cout, Sum[3:1]} === $past({Cout, Sum[3:1]}, 2))
    );

    // Changing top-level Cin does not change upper outputs when the LSB carry is 0.
    check_cin_change_ignored_with_zero_lsb_carry: assert property (
        @(posedge clk)
        ($past(1'b1) &&
         $stable(A) &&
         $stable(B) &&
         (Cin != $past(Cin)) &&
         (A[0] == 1'b0) &&
         (B[0] == 1'b0)) |->
        ({Cout, Sum[3:1]} === $past({Cout, Sum[3:1]}))
    );

    // Changing top-level Cin does not change upper outputs when the LSB carry is 1.
    check_cin_change_ignored_with_one_lsb_carry: assert property (
        @(posedge clk)
        ($past(1'b1) &&
         $stable(A) &&
         $stable(B) &&
         (Cin != $past(Cin)) &&
         (A[0] == 1'b1) &&
         (B[0] == 1'b1)) |->
        ({Cout, Sum[3:1]} === $past({Cout, Sum[3:1]}))
    );

endmodule