module top_module_sva (
    input  logic clk,              // External clock for checker (RTL is purely combinational)
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [31:0] sum
);
    // Sum must equal a + b (mod 2^32).
    check_sum_add32: assert property (
        @(posedge clk) disable iff (1'b0) sum == (a + b)
    );

    // Lower 16 bits must equal a[15:0] + b[15:0] (mod 2^16).
    check_lower16_add: assert property (
        @(posedge clk) disable iff (1'b0) sum[15:0] == (a[15:0] + b[15:0])
    );

    // Upper 16 bits must equal a[31:16] + b[31:16] + carry from lower 16 bits (mod 2^16).
    check_upper16_with_carry_from_lower: assert property (
        @(posedge clk) disable iff (1'b0)
            sum[31:16] == (
                ({1'b0, a[31:16]} + {1'b0, b[31:16]} + (({1'b0, a[15:0]} + {1'b0, b[15:0]})[16]))
            )[15:0]
    );

    // LSB must be XOR of input LSBs (since carry-in to bit 0 is 0).
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (1'b0) sum[0] == (a[0] ^ b[0])
    );

    // If both inputs are zero, sum must be zero.
    check_zero_plus_zero: assert property (
        @(posedge clk) disable iff (1'b0) (a == 32'd0 && b == 32'd0) |-> (sum == 32'd0)
    );

    // If a is zero, sum must equal b.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (a == 32'd0) |-> (sum == b)
    );

    // If b is zero, sum must equal a.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (b == 32'd0) |-> (sum == a)
    );

    // Full-width overflow wraps: 0xFFFF_FFFF + 1 -> 0x0000_0000.
    check_full_overflow_wrap: assert property (
        @(posedge clk) disable iff (1'b0) (a == 32'hFFFF_FFFF && b == 32'd1) |-> (sum == 32'd0)
    );

    // If inputs hold their values, output must hold as well (purely combinational function).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // Commutativity check: sum equals b + a as well.
    check_commutativity: assert property (
        @(posedge clk) disable iff (1'b0) sum == (b + a)
    );
endmodule