module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic a, b, c,
    input logic [7:0] q
);
    ///// Reset behavior /////
    // While reset is asserted, top-level q must be all zeros.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

    ///// Structural masking from mux_out (zero-extended) /////
    // Upper nibble of q is always zero due to 4-bit mux_out AND with 8-bit.
    check_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) (q[7:4] == 4'b0000)
    );

    ///// Multiplexer masking on lower nibble /////
    // For abc=000 (mask 0001), lower bits [3:1] must be zero.
    mask_zero_000: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b000) |-> (q[3:1] == 3'b000)
    );
    // For abc=001 (mask 0010), bits [3:2] and bit0 must be zero.
    mask_zero_001: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b001) |-> (q[3:2] == 2'b00) && (q[0] == 1'b0)
    );
    // For abc=010 (mask 0100), bit3 and bits [1:0] must be zero.
    mask_zero_010: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b010) |-> (q[3] == 1'b0) && (q[1:0] == 2'b00)
    );
    // For abc=011 (mask 1000), bits [2:0] must be zero.
    mask_zero_011: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b011) |-> (q[2:0] == 3'b000)
    );
    // For abc=100 (mask 0011), bits [3:2] must be zero.
    mask_zero_100: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b100) |-> (q[3:2] == 2'b00)
    );
    // For abc=101 (mask 0110), bit3 and bit0 must be zero.
    mask_zero_101: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b101) |-> (q[3] == 1'b0) && (q[0] == 1'b0)
    );
    // For abc=110 (mask 1100), bits [1:0] must be zero.
    mask_zero_110: assert property (
        @(posedge clk) disable iff (reset) ({c,b,a} == 3'b110) |-> (q[1:0] == 2'b00)
    );

    ///// Post-reset timing from flip_flops /////
    // After reset deasserts, q remains zero for the next 7 cycles.
    hold_zero_7_cycles_after_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> (q == 8'h00)[*7]
    );
endmodule