module Adder_sva (
    input logic clk,
    input logic [3:0] din_a,
    input logic [3:0] din_b,
    input logic [3:0] din_c,
    input logic [3:0] dout
);
    // No clock/reset in DUT; pure combinational. Assertions sample on external clk.

    // dout equals lower 4 bits of din_a + din_b.
    check_sum_mod16: assert property (
        @(posedge clk) dout == ({1'b0, din_a} + {1'b0, din_b})[3:0]
    );

    // Zero identity: when din_a is 0, dout equals din_b.
    check_zero_identity_a: assert property (
        @(posedge clk) (din_a == 4'h0) |-> (dout == din_b)
    );

    // Zero identity: when din_b is 0, dout equals din_a.
    check_zero_identity_b: assert property (
        @(posedge clk) (din_b == 4'h0) |-> (dout == din_a)
    );

    // Commutativity cross-check: dout also matches (din_b + din_a) LSBs.
    check_commutative_sum: assert property (
        @(posedge clk) dout == ({1'b0, din_b} + {1'b0, din_a})[3:0]
    );

    // LSB of sum equals XOR of input LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) dout[0] == (din_a[0] ^ din_b[0])
    );

    // Output stable if din_a and din_b are both stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(din_a) && $stable(din_b)) |-> $stable(dout)
    );

    // Output change implies at least one of din_a or din_b changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) $changed(dout) |-> (!$stable(din_a) || !$stable(din_b))
    );

    // Changes on din_c alone do not affect dout.
    check_din_c_independence: assert property (
        @(posedge clk) ($changed(din_c) && $stable(din_a) && $stable(din_b)) |-> $stable(dout)
    );

    // Specific wrap case: F + F -> E (mod 16).
    check_ff_wraps_to_e: assert property (
        @(posedge clk) ((din_a == 4'hF) && (din_b == 4'hF)) |-> (dout == 4'hE)
    );

    // Specific wrap case: F + 1 -> 0 (mod 16).
    check_f_plus_one_wraps_to_zero: assert property (
        @(posedge clk) ((din_a == 4'hF) && (din_b == 4'h1)) |-> (dout == 4'h0)
    );

endmodule