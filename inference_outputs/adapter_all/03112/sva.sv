module adder_4bit_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] s,
    input logic       cout
);

    // Combined outputs equal the 5-bit sum of a, b, and cin.
    check_full_sum: assert property (
        @($global_clock) {cout, s} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // s is the low 4 bits of the arithmetic result.
    check_sum_low_bits: assert property (
        @($global_clock) s == (({1'b0, a} + {1'b0, b} + cin)[3:0])
    );

    // cout is the carry-out bit of the arithmetic result.
    check_carry_out: assert property (
        @($global_clock) cout == (({1'b0, a} + {1'b0, b} + cin)[4])
    );

    // Adding zero on b with cin low passes a through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (b == 4'h0 && cin == 1'b0) |-> (s == a && cout == 1'b0)
    );

    // Adding zero on a with cin low passes b through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (a == 4'h0 && cin == 1'b0) |-> (s == b && cout == 1'b0)
    );

    // With a and b zero, cout follows cin and s is zero.
    check_zero_inputs: assert property (
        @($global_clock) (a == 4'h0 && b == 4'h0) |-> (s == 4'h0 && cout == cin)
    );

    // With a and b at 4'hF, cout is high and s is the 4-bit sum of cin and 4'h1.
    check_max_plus_max: assert property (
        @($global_clock) (a == 4'hF && b == 4'hF) |-> (s == (cin ? 4'h0 : 4'h1) && cout == 1'b1)
    );

    // With a at 4'hF and b at 4'h1, cout is high and s is cin.
    check_f_plus_one: assert property (
        @($global_clock) (a == 4'hF && b == 4'h1) |-> (s == cin && cout == 1'b1)
    );

    // With a at 4'h0 and b at 4'h1, cout is cin and s is the 4-bit sum of cin and 4'h1.
    check_zero_plus_one: assert property (
        @($global_clock) (a == 4'h0 && b == 4'h1) |-> (s == (cin ? 4'h1 : 4'h0) && cout == cin)
    );

    // With a at 4'hF and b at 4'h0, cout is cin and s is the 4-bit sum of cin and 4'h1.
    check_f_plus_zero: assert property (
        @($global_clock) (a == 4'hF && b == 4'h0) |-> (s == (cin ? 4'h1 : 4'h0) && cout == cin)
    );

endmodule