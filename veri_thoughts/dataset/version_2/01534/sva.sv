module four_bit_adder_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       cin,
    input  logic [3:0] s,
    input  logic       cout
);

    ///// Functional correctness /////
    // Combined {cout,s} equals the 5 LSBs of a+b+cin (pure combinational adder correctness).
    check_arith_sum_5lsb: assert property (
        @(posedge CLK) disable iff (!RESETn)
            {cout, s} == (a + b + cin)[4:0]
    );

    // LSB sum bit is XOR of a[0], b[0], and cin.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
            s[0] == (a[0] ^ b[0] ^ cin)
    );

    // s[1] is XOR of a[1], b[1], and carry from bit0.
    check_sum_bit1_with_c0: assert property (
        @(posedge CLK) disable iff (!RESETn)
            s[1] == (a[1] ^ b[1] ^ ( (a[0] & b[0]) | (cin & (a[0] ^ b[0])) ))
    );

    // s[2] is XOR of a[2], b[2], and carry from bit1.
    check_sum_bit2_with_c1: assert property (
        @(posedge CLK) disable iff (!RESETn)
            s[2] == (a[2] ^ b[2] ^ (
                        (a[1] & b[1]) |
                        ( ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1]) )
                    ))
    );

    // s[3] is XOR of a[3], b[3], and carry from bit2.
    check_sum_bit3_with_c2: assert property (
        @(posedge CLK) disable iff (!RESETn)
            s[3] == (a[3] ^ b[3] ^ (
                        (a[2] & b[2]) |
                        ( ( (a[1] & b[1]) |
                            ( ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1]) )
                          ) & (a[2] ^ b[2]) )
                    ))
    );

    // cout equals carry from bit3 (ripple of generated/propagated carries).
    check_cout_from_c3: assert property (
        @(posedge CLK) disable iff (!RESETn)
            cout == (
                (a[3] & b[3]) |
                ( (
                    (a[2] & b[2]) |
                    ( ( (a[1] & b[1]) |
                        ( ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1]) )
                      ) & (a[2] ^ b[2]) )
                  ) & (a[3] ^ b[3]) )
            )
    );

    // cout is high iff a+b+cin exceeds 4'hF (overflow of 4-bit sum).
    check_cout_overflow_flag: assert property (
        @(posedge CLK) disable iff (!RESETn)
            cout == ((a + b + cin) > 4'hF)
    );

    ///// Simple corner cases /////
    // With a=0 and b=0, s equals cin in bit0 and zeros elsewhere; cout is 0.
    check_zero_inputs_passthrough_cin: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((a == 4'b0000) && (b == 4'b0000)) |->
                (s == {3'b000, cin}) && (cout == 1'b0)
    );

    // With a=0 and cin=0, s equals b and cout is 0.
    check_add_b_when_a_zero_cin_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((a == 4'b0000) && (cin == 1'b0)) |->
                (s == b) && (cout == 1'b0)
    );

endmodule