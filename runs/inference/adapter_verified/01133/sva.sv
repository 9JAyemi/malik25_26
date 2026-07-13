module address_to_signal_sva (
    input logic [9:0] address,
    input logic       clock,
    input logic [11:0] q
);

// q equals address shifted left by 2 with 00 appended.
    check_q_shift_and_zero: assert property (
        @(posedge clock) q == {address, 2'b00}
    );

// LSBs are always zero due to zero extension.
    check_q_lsb_zero: assert property (
        @(posedge clock) q[1:0] == 2'b00
    );

// Upper 9 bits match address.
    check_q_upper_matches_address: assert property (
        @(posedge clock) q[11:2] == address
    );

// When clock is low, q equals address shifted left by 2.
    check_q_when_clock_low: assert property (
        @(posedge clock) !clock |-> (q == {address, 2'b00})
    );

// When clock is high, q equals bitwise inversion of address shifted left by 2.
    check_q_when_clock_high: assert property (
        @(posedge clock) clock |-> (q == ~{address, 2'b00})
    );

endmodule
