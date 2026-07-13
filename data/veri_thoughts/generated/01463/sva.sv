module arithmetic_module_sva (
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic b,
    input logic Boo_ba3,
    input logic c,
    input logic [3:0] f4_dotnamed,
    input logic [3:0] f1_dotnamed,
    input logic [3:0] f2_dotnamed,
    input logic [3:0] f3_dotnamed
);
    // No clock/reset in RTL; all logic is combinational. Sample assertions on any input edge.

    // f4 equals the sum of sub-results.
    check_top_sum_correct: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f4_dotnamed == (f1_dotnamed + f2_dotnamed + f3_dotnamed))
    );

    // SubA: shift-left of 1-bit input results in all zeros (assigned into 4 bits).
    check_suba_zero: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f1_dotnamed == 4'd0)
    );

    // SubB: upper bits are always zero due to 1-bit addition assigned into 4 bits.
    check_subb_upper_zero: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f2_dotnamed[3:1] == 3'b000)
    );

    // SubB: LSB equals a XOR b (1-bit + 1-bit with truncated carry).
    check_subb_lsb_xor: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f2_dotnamed[0] == (Boo_ba2 ^ b))
    );

    // SubC: upper bits are always zero due to 1-bit subtraction assigned into 4 bits.
    check_subc_upper_zero: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f3_dotnamed[3:1] == 3'b000)
    );

    // SubC: LSB equals a XOR c (1-bit subtraction modulo 2).
    check_subc_lsb_xor: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f3_dotnamed[0] == (Boo_ba3 ^ c))
    );

    // f4 LSB equals parity (XOR) of the sub-results' LSBs.
    check_f4_lsb_parity: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f4_dotnamed[0] == (f1_dotnamed[0] ^ f2_dotnamed[0] ^ f3_dotnamed[0]))
    );

    // f4 bit1 equals carry from adding f2[0] and f3[0] (since other bit1 sources are zero).
    check_f4_bit1_carry_from_lsb: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f4_dotnamed[1] == (f2_dotnamed[0] & f3_dotnamed[0]))
    );

    // f4 upper bits [3:2] are always zero.
    check_f4_upper_zero: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f4_dotnamed[3:2] == 2'b00)
    );

    // Direct functional relation: f4 equals (Boo_ba2^b) + (Boo_ba3^c).
    check_top_direct_function: assert property (
        @(posedge Boo_ba1 or negedge Boo_ba1 or
          posedge Boo_ba2 or negedge Boo_ba2 or
          posedge b       or negedge b       or
          posedge Boo_ba3 or negedge Boo_ba3 or
          posedge c       or negedge c)
        (f4_dotnamed == {{3{1'b0}}, 1'b0} + {{3{1'b0}}, (Boo_ba2 ^ b)} + {{3{1'b0}}, (Boo_ba3 ^ c)})
    );

endmodule