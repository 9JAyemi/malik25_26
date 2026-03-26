module mux_and_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic        sel_b1,
    input logic        sel_b2,
    input logic [3:0]  c,
    input logic [7:0]  out
);

    // Output matches the selected input masked by zero-extended c.
    check_out_matches_rtl_function: assert property (
        @(posedge clk)
        out == (((sel_b1 & sel_b2) ? b : a) & {4'b0000, c})
    );

    // When both select inputs are high, b drives the masked output.
    check_selects_choose_b: assert property (
        @(posedge clk)
        (sel_b1 & sel_b2) |-> (out == (b & {4'b0000, c}))
    );

    // When either select input is low, a drives the masked output.
    check_selects_choose_a: assert property (
        @(posedge clk)
        !(sel_b1 & sel_b2) |-> (out == (a & {4'b0000, c}))
    );

    // Upper output bits are always zero because c is only 4 bits wide.
    check_upper_nibble_forced_zero: assert property (
        @(posedge clk)
        out[7:4] == 4'b0000
    );

    // A zero mask clears the entire output.
    check_zero_mask_clears_output: assert property (
        @(posedge clk)
        (c == 4'h0) |-> (out == 8'h00)
    );

endmodule