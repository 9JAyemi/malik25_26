module Adder_sva (
    input logic [3:0] din_a,
    input logic [3:0] din_b,
    input logic [3:0] din_c,
    input logic [3:0] dout
);
    // No clock/reset in RTL; pure combinational; using clockless concurrent assertions.

    // dout equals the lower 4 bits of din_a + din_b + din_c.
    check_dout_is_sum_mod16: assert property (
        dout == ((din_a + din_b + din_c) & 4'hF)
    );

    // LSB of dout equals XOR of input LSBs (no carry-in to bit 0).
    check_lsb_xor3: assert property (
        dout[0] == (din_a[0] ^ din_b[0] ^ din_c[0])
    );

    // If din_c is zero, dout equals (din_a + din_b) mod 16.
    check_zero_identity_c: assert property (
        (din_c != 4'b0) || (dout == ((din_a + din_b) & 4'hF))
    );

    // If din_b is zero, dout equals (din_a + din_c) mod 16.
    check_zero_identity_b: assert property (
        (din_b != 4'b0) || (dout == ((din_a + din_c) & 4'hF))
    );

    // If din_a is zero, dout equals (din_b + din_c) mod 16.
    check_zero_identity_a: assert property (
        (din_a != 4'b0) || (dout == ((din_b + din_c) & 4'hF))
    );
endmodule