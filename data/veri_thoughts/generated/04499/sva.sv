module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic sum,
    input logic cout
);

    // Sum is the XOR of a, b, and cin.
    check_sum_xor_chain: assert property (
        @(posedge clk) sum == ((a ^ b) ^ cin)
    );

    // Carry out matches the OR of the two half-adder carry terms.
    check_cout_from_half_adders: assert property (
        @(posedge clk) cout == ((a & b) | ((a ^ b) & cin))
    );

    // The concatenated outputs equal the 2-bit sum of the inputs.
    check_full_adder_arithmetic: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + {1'b0, cin})
    );

    // With cin low, the block behaves like a half adder on a and b.
    check_cin_low_half_adder_mode: assert property (
        @(posedge clk) !cin |-> ((sum == (a ^ b)) && (cout == (a & b)))
    );

    // With cin high, sum inverts a^b and carry becomes a|b.
    check_cin_high_add_one_mode: assert property (
        @(posedge clk) cin |-> ((sum == ~(a ^ b)) && (cout == (a | b)))
    );

endmodule