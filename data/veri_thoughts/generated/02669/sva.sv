module top_module_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic signed [63:0] product
);
    // Notes: No clock/reset in RTL; purely combinational. clk here is a sampling clock for SVA.

    // Full product equals concatenation of four signed 8x8 products.
    check_full_concat: assert property (
        @(posedge clk) product == {
            ($signed(a[31:24]) * $signed(b[31:24])),
            ($signed(a[23:16]) * $signed(b[23:16])),
            ($signed(a[15:8])  * $signed(b[15:8])),
            ($signed(a[7:0])   * $signed(b[7:0]))
        }
    );

    // Low 16 bits equal signed multiply of low bytes.
    check_seg0_mapping: assert property (
        @(posedge clk) product[15:0] == ($signed(a[7:0]) * $signed(b[7:0]))
    );

    // Bits [31:16] equal signed multiply of second byte.
    check_seg1_mapping: assert property (
        @(posedge clk) product[31:16] == ($signed(a[15:8]) * $signed(b[15:8]))
    );

    // Bits [47:32] equal signed multiply of third byte.
    check_seg2_mapping: assert property (
        @(posedge clk) product[47:32] == ($signed(a[23:16]) * $signed(b[23:16]))
    );

    // High 16 bits equal signed multiply of high bytes.
    check_seg3_mapping: assert property (
        @(posedge clk) product[63:48] == ($signed(a[31:24]) * $signed(b[31:24]))
    );

    // If low bytes of a and b are stable, low 16 bits of product are stable.
    check_seg0_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(a[7:0]) && $stable(b[7:0]) |-> $stable(product[15:0])
    );

    // If second bytes of a and b are stable, bits [31:16] of product are stable.
    check_seg1_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(a[15:8]) && $stable(b[15:8]) |-> $stable(product[31:16])
    );

    // If third bytes of a and b are stable, bits [47:32] of product are stable.
    check_seg2_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(a[23:16]) && $stable(b[23:16]) |-> $stable(product[47:32])
    );

    // If high bytes of a and b are stable, high 16 bits of product are stable.
    check_seg3_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(a[31:24]) && $stable(b[31:24]) |-> $stable(product[63:48])
    );

    // If either operand is zero, the entire product bus is zero.
    check_zero_operand_zero_product: assert property (
        @(posedge clk) ((a == 32'sd0) || (b == 32'sd0)) |-> (product == 64'sd0)
    );

endmodule