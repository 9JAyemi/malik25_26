module Change2Negedge_sva (
    input logic        hsync_in,
    input logic        vsync_in,
    input logic        blnk_in,
    input logic [23:0] rgb_in,
    input logic        clk,
    input logic        rst,
    input logic        hsync_out,
    input logic        vsync_out,
    input logic        blnk_out,
    input logic [23:0] rgb_out
);

    // A sampled reset cycle leaves all registered outputs at zero by the next negedge.
    check_reset_clears_outputs: assert property (
        @(negedge clk)
        rst |=> ({hsync_out, vsync_out, blnk_out, rgb_out} == 27'b0)
    );

    // Without reset, the next negedge outputs are either reset-zero or the prior negedge input sample.
    check_negedge_transfer: assert property (
        @(negedge clk) disable iff (rst)
        1'b1 |=> (
            ({hsync_out, vsync_out, blnk_out, rgb_out} == 27'b0) ||
            ({hsync_out, vsync_out, blnk_out, rgb_out} ==
             $past({hsync_in, vsync_in, blnk_in, rgb_in}))
        )
    );

endmodule