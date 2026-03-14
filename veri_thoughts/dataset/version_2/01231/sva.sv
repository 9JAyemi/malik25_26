module top_module_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic select,
    input logic [3:0] out
);
    // No clock/reset in DUT; combinational logic; assertions sample on external CLK.

    // When select is 0, out must equal a.
    check_mux_select0: assert property (
        @(posedge CLK) (select == 1'b0) |-> (out == a)
    );

    // When select is 1, out must equal the 4-bit sum a + b.
    check_mux_select1_sum: assert property (
        @(posedge CLK) (select == 1'b1) |-> (out == (a + b))
    );

    // If select is 1 and b is zero, out equals a.
    check_add_zero_b: assert property (
        @(posedge CLK) (select && (b == 4'b0000)) |-> (out == a)
    );

    // If select is 1 and a is zero, out equals b.
    check_add_zero_a: assert property (
        @(posedge CLK) (select && (a == 4'b0000)) |-> (out == b)
    );

    // In add path, bit0 is XOR of a[0] and b[0] (carry_in = 0).
    check_adder_bit0: assert property (
        @(posedge CLK) select |-> (out[0] == (a[0] ^ b[0]))
    );

    // In add path, bit1 equals a[1] ^ b[1] ^ carry0 where carry0 = a[0] & b[0].
    check_adder_bit1: assert property (
        @(posedge CLK) select |-> (out[1] == (a[1] ^ b[1] ^ (a[0] & b[0])))
    );

    // In add path, bit2 equals a[2] ^ b[2] ^ carry1 with carry1 = (a1&b1) | ((a1^b1)&(a0&b0)).
    check_adder_bit2: assert property (
        @(posedge CLK) select |-> (out[2] == (a[2] ^ b[2] ^ ((a[1] & b[1]) | ((a[1] ^ b[1]) & (a[0] & b[0])))))
    );

    // In add path, bit3 equals a[3] ^ b[3] ^ carry2; carry2 = (a2&b2)|((a2^b2)&carry1).
    check_adder_bit3: assert property (
        @(posedge CLK) select |-> (
            out[3] == (a[3] ^ b[3] ^ (
                (a[2] & b[2]) | ((a[2] ^ b[2]) & ((a[1] & b[1]) | ((a[1] ^ b[1]) & (a[0] & b[0]))))
            ))
        )
    );

endmodule