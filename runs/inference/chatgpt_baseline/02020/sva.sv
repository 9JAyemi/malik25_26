module four_bit_adder_sva (
    input logic clk,            // sampling clock for SVA (RTL is combinational)
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // Analysis: No clock/reset in RTL; pure combinational; behavior: sum=(a+b+cin)[3:0], cout=((a+b+cin)>4'hF).

    // sum equals lower 4 bits of a+b+cin.
    check_sum_mod16: assert property (
        @(posedge clk) sum == (({1'b0,a} + {1'b0,b} + cin)[3:0])
    );

    // cout equals ((a+b+cin) > 4'hF) as written in the RTL.
    check_cout_comparator: assert property (
        @(posedge clk) cout == ((a + b + cin) > 4'hF)
    );

    // When no overflow in 5-bit addition, {cout,sum} equals the 5-bit sum.
    check_pair_no_overflow: assert property (
        @(posedge clk) (({1'b0,a} + {1'b0,b} + cin) <= 5'd15) |-> ({cout, sum} == ({1'b0,a} + {1'b0,b} + cin))
    );

    // Outputs remain stable when all inputs are stable (combinational purity).
    check_outputs_pure_function: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(cin)) |-> ($stable(sum) && $stable(cout))
    );

    // sum can only change if at least one input changed.
    check_sum_change_requires_input_change: assert property (
        @(posedge clk) (!$stable(sum)) |-> (!$stable(a) || !$stable(b) || !$stable(cin))
    );

    // cout can only change if at least one input changed.
    check_cout_change_requires_input_change: assert property (
        @(posedge clk) (!$stable(cout)) |-> (!$stable(a) || !$stable(b) || !$stable(cin))
    );

    // With b==0 and cin==0, sum passes a and cout is 0.
    check_transparency_b_zero_cin_zero: assert property (
        @(posedge clk) (b == 4'd0 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // With a==0 and cin==0, sum passes b and cout is 0.
    check_transparency_a_zero_cin_zero: assert property (
        @(posedge clk) (a == 4'd0 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // With a==0 and b==0, sum equals cin and cout is 0.
    check_sum_equals_cin_when_a_b_zero: assert property (
        @(posedge clk) (a == 4'd0 && b == 4'd0) |-> (sum == {3'b000, cin} && cout == 1'b0)
    );

    // Least-significant sum bit equals XOR of inputs' LSBs.
    check_sum_bit0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

endmodule