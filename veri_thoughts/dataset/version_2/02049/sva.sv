module top_module_sva (
    input logic clk,
    input logic reset, // synchronous active-high
    input logic [3:0] D0,
    input logic [15:0] D1,
    input logic select,
    input logic L,
    input logic [19:0] out
);
    // Clk/reset: clk posedge, reset sync active-high. Sequential logic (two rotating/loadable shift regs). out = (Q1 | Q0) zero-extended to 20b; out[19:16] are always 0.

    // Synchronous reset drives out to 0 on the next cycle.
    reset_clears_out_next: assert property (
        @(posedge clk) reset |=> (out == 20'h00000)
    );

    // The upper 4 bits of out are always zero due to zero-extension to 20 bits.
    invariant_top_bits_zero: assert property (
        @(posedge clk) disable iff (reset) (out[19:16] == 4'b0000)
    );

    // Loading sr1 (L & select) sets out[15:4] to D1[15:4] on the next cycle.
    sr1_load_sets_upper: assert property (
        @(posedge clk) disable iff (reset)
            (L && select) |=> (reset || (out[15:4] == $past(D1[15:4])))
    );

    // When sr1 is not loaded, out[15:5] rotates left by 1 (reflecting sr1 rotation).
    sr1_rotate_upper_when_not_loaded: assert property (
        @(posedge clk) disable iff (reset)
            (!(L && select)) |=> (reset || (out[15:5] == $past(out[14:4])))
    );

    // Loading sr1 guarantees next-cycle out[3:0] includes D1[3:0] (OR dominance).
    sr1_load_includes_lower_nibble: assert property (
        @(posedge clk) disable iff (reset)
            (L && select) |=> (reset || ((out[3:0] & $past(D1[3:0])) == $past(D1[3:0])))
    );

    // Loading sr0 guarantees next-cycle out[3:0] includes D0[3:0] (OR dominance).
    sr0_load_includes_lower_nibble: assert property (
        @(posedge clk) disable iff (reset)
            (L && !select) |=> (reset || ((out[3:0] & $past(D0[3:0])) == $past(D0[3:0])))
    );

    // If sr1 loads zeros in upper 12 bits, out[15:4] becomes zero next cycle.
    sr1_load_upper_zeros: assert property (
        @(posedge clk) disable iff (reset)
            (L && select && (D1[15:4] == 12'h000)) |=> (reset || (out[15:4] == 12'h000))
    );

    // If sr1 loads all ones in upper 12 bits, out[15:4] becomes all ones next cycle.
    sr1_load_upper_ones: assert property (
        @(posedge clk) disable iff (reset)
            (L && select && (D1[15:4] == 12'hFFF)) |=> (reset || (out[15:4] == 12'hFFF))
    );

    // If sr0 loads 4'hF, out[3:0] becomes 4'hF next cycle (OR with anything yields all ones).
    sr0_load_lower_all_ones: assert property (
        @(posedge clk) disable iff (reset)
            (L && !select && (D0 == 4'hF)) |=> (reset || (out[3:0] == 4'hF))
    );

    // If sr1 loads 4'hF in low nibble, out[3:0] becomes 4'hF next cycle.
    sr1_load_lower_all_ones: assert property (
        @(posedge clk) disable iff (reset)
            (L && select && (D1[3:0] == 4'hF)) |=> (reset || (out[3:0] == 4'hF))
    );
endmodule