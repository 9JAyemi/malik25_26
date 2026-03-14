module macc_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out
);

    // Reset sets out to 0 on the following clock.
    check_reset_clears_out_next: assert property (
        @(posedge clk) reset |=> (out == 32'd0)
    );

    // If reset is held for consecutive cycles, out stays 0.
    check_reset_held_keeps_out_zero: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (out == 32'd0)
    );

    // First cycle after reset deasserts updates from zero with current product (mod 2^32).
    check_first_cycle_after_reset_update: assert property (
        @(posedge clk) $fell(reset) |=> (out == (a * b)[31:0])
    );

    // When not in reset, out updates as previous out plus a*b (mod 2^32).
    check_accumulation_update: assert property (
        @(posedge clk) disable iff (reset) out == (($past(out) + (a * b))[31:0])
    );

    // When either multiplicand is zero, out holds its previous value (no change).
    check_zero_multiplicand_holds_output: assert property (
        @(posedge clk) disable iff (reset) ((a == 32'd0) || (b == 32'd0)) |-> (out == $past(out))
    );

    // If low 32 bits of the product are zero, out holds its previous value.
    check_low32_product_zero_holds_output: assert property (
        @(posedge clk) disable iff (reset) (((a * b)[31:0] == 32'd0)) |-> (out == $past(out))
    );

    // The per-cycle delta equals low 32 bits of a*b (mod 2^32).
    check_delta_matches_low_product: assert property (
        @(posedge clk) disable iff (reset) (out - $past(out)) == (a * b)[31:0]
    );

endmodule