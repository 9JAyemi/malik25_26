module top_module_sva (
    input logic clk,                  // External verification clock (DUT has no clock/reset)
    input logic [99:0] a, b,
    input logic cin,
    input logic cout,
    input logic [99:0] sum
);
    // DUT is purely combinational: {cout,sum} == a + b + cin (101-bit result)

    function automatic logic [100:0] full_add101 (
        input logic [99:0] aa,
        input logic [99:0] bb,
        input logic c
    );
        full_add101 = {1'b0, aa} + {1'b0, bb} + {{100{1'b0}}, c};
    endfunction

    // Sum and carry-out equal the 101-bit addition of a, b, and cin.
    check_full_addition_concat: assert property (
        @(posedge clk) {cout, sum} == full_add101(a, b, cin)
    );

    // Sum equals the low 100 bits of the 101-bit addition.
    check_sum_lowbits: assert property (
        @(posedge clk) sum == full_add101(a, b, cin)[99:0]
    );

    // cout equals the MSB (bit 100) of the 101-bit addition.
    check_cout_msb: assert property (
        @(posedge clk) cout == full_add101(a, b, cin)[100]
    );

    // If b==0 and cin==0, output equals a with no carry.
    check_identity_b_zero_no_cin: assert property (
        @(posedge clk) (b == 100'b0 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // If a==0 and cin==0, output equals b with no carry.
    check_identity_a_zero_no_cin: assert property (
        @(posedge clk) (a == 100'b0 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // If a==0 and b==0, sum is cin in bit0 and cout is 0.
    check_zero_plus_zero: assert property (
        @(posedge clk) (a == 100'b0 && b == 100'b0) |-> (sum == {{99{1'b0}}, cin} && cout == 1'b0)
    );

    // If a and b are all ones and cin==1, sum is all ones and cout is 1.
    check_all_ones_plus_one: assert property (
        @(posedge clk) (a == {100{1'b1}} && b == {100{1'b1}} && cin == 1'b1) |-> (sum == {100{1'b1}} && cout == 1'b1)
    );

    // If b is bitwise NOT of a and cin==0, sum is all ones and cout is 0.
    check_complement_no_cin: assert property (
        @(posedge clk) (b == ~a && cin == 1'b0) |-> (sum == {100{1'b1}} && cout == 1'b0)
    );

    // If b is bitwise NOT of a and cin==1, sum is zero and cout is 1.
    check_complement_with_cin: assert property (
        @(posedge clk) (b == ~a && cin == 1'b1) |-> (sum == {100{1'b0}} && cout == 1'b1)
    );

    // LSB of sum equals XOR of a[0], b[0], and cin.
    check_lsb_xor_rule: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

endmodule