module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum,
    input logic CLK
);
    // DUT has no clock/reset; pure combinational sum = (a + b)[3:0]; assertions sample on CLK.

    // Sum equals 4-bit truncated addition of a and b.
    check_sum_truncated_add: assert property (
        @(posedge CLK) sum == (a + b)[3:0]
    );

    // LSB equals XOR of a[0] and b[0].
    check_lsb_xor: assert property (
        @(posedge CLK) sum[0] == (a[0] ^ b[0])
    );

    // Bit1 follows ripple-carry equation.
    check_bit1_equation: assert property (
        @(posedge CLK) sum[1] == (a[1] ^ b[1] ^ (a[0] & b[0]))
    );

    // Bit2 follows ripple-carry equation.
    check_bit2_equation: assert property (
        @(posedge CLK) sum[2] == (a[2] ^ b[2] ^ ( (a[1] & b[1]) | ((a[1] ^ b[1]) & (a[0] & b[0])) ))
    );

    // Bit3 follows ripple-carry equation.
    check_bit3_equation: assert property (
        @(posedge CLK) sum[3] == (a[3] ^ b[3] ^ ( (a[2] & b[2]) | ((a[2] ^ b[2]) & ( (a[1] & b[1]) | ((a[1] ^ b[1]) & (a[0] & b[0])) ) ) ))
    );

    // Adding zero passes a through.
    check_b_zero_passthrough: assert property (
        @(posedge CLK) (b == 4'd0) |-> (sum == a)
    );

    // Adding zero passes b through.
    check_a_zero_passthrough: assert property (
        @(posedge CLK) (a == 4'd0) |-> (sum == b)
    );

    // Commutativity consistency with built-in addition.
    check_commutativity: assert property (
        @(posedge CLK) sum == (b + a)[3:0]
    );

endmodule