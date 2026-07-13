module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);
    ///// Functional equivalence checks /////
    // {cout,sum} equals zero-extended 4-bit (a + b + cin).
    check_concat_zero_extended: assert property (
        @(posedge cin) {cout, sum} == {1'b0, (a + b + cin)}
    );
    // cout is always 0 (addition width is 4 bits on RHS).
    check_cout_always_zero: assert property (
        @(posedge cin) cout == 1'b0
    );
    // sum equals 4-bit (a + b + cin) modulo 16.
    check_sum_mod_add: assert property (
        @(posedge cin) sum == (a + b + cin)
    );

    ///// Bit-level full-adder relations derived from a + b + cin /////
    // LSB: sum[0] = a0 ^ b0 ^ cin.
    check_sum_bit0_xor: assert property (
        @(posedge cin) sum[0] == (a[0] ^ b[0] ^ cin)
    );
    // sum[1] with carry from bit 0.
    check_sum_bit1_full_adder: assert property (
        @(posedge cin) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin)))
    );
    // sum[2] with propagated carry.
    check_sum_bit2_full_adder: assert property (
        @(posedge cin)
            sum[2] == (a[2] ^ b[2] ^
                       (((a[1] & b[1]) | ((a[1] ^ b[1]) & ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin))))))
    );
    // sum[3] with propagated carry.
    check_sum_bit3_full_adder: assert property (
        @(posedge cin)
            sum[3] == (a[3] ^ b[3] ^
                       ( (a[2] & b[2]) |
                         ( (a[2] ^ b[2]) &
                           ( (a[1] & b[1]) |
                             ( (a[1] ^ b[1]) &
                               ( (a[0] & b[0]) | ( (a[0] ^ b[0]) & cin ) )
                             )
                           )
                         )
                       )
            )
    );

    ///// Corner cases by cin value /////
    // When cin rises (cin=1), output equals a + b + 1 with zero-extended carry.
    check_sum_when_cin1: assert property (
        @(posedge cin) {cout, sum} == {1'b0, (a + b + 1'b1)}
    );
    // When cin falls (cin=0), output equals a + b with zero-extended carry.
    check_sum_when_cin0: assert property (
        @(negedge cin) {cout, sum} == {1'b0, (a + b)}
    );
    // cout is 0 also when cin falls.
    check_cout_zero_negedge: assert property (
        @(negedge cin) cout == 1'b0
    );
endmodule