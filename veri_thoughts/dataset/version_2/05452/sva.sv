module lcd_driver_sva #(
    parameter int n = 8
)(
    input logic       clk,
    input logic [7:0] ascii,
    input logic [n-1:0] seg
);

generate
if (n >= 8) begin : gen_lcd_driver_checks

    // seg[0] matches the ASCII decode for segment a.
    check_seg_a_decode: assert property (
        @(posedge clk)
        seg[0] == (ascii == 8'h41 || ascii == 8'h61 || ascii == 8'hC1 || ascii == 8'hE1)
    );

    // seg[1] matches the ASCII decode for segment b.
    check_seg_b_decode: assert property (
        @(posedge clk)
        seg[1] == (ascii == 8'h42 || ascii == 8'h62 || ascii == 8'hC2 || ascii == 8'hE2)
    );

    // seg[2] matches the ASCII decode for segment c.
    check_seg_c_decode: assert property (
        @(posedge clk)
        seg[2] == (ascii == 8'h43 || ascii == 8'h63 || ascii == 8'hC3 || ascii == 8'hE3)
    );

    // seg[3] matches the ASCII decode for segment d.
    check_seg_d_decode: assert property (
        @(posedge clk)
        seg[3] == (ascii == 8'h44 || ascii == 8'h64 || ascii == 8'hC4 || ascii == 8'hE4)
    );

    // seg[4] matches the ASCII decode for segment e.
    check_seg_e_decode: assert property (
        @(posedge clk)
        seg[4] == (ascii == 8'h45 || ascii == 8'h65 || ascii == 8'hC5 || ascii == 8'hE5)
    );

    // seg[5] matches the ASCII decode for segment f.
    check_seg_f_decode: assert property (
        @(posedge clk)
        seg[5] == (ascii == 8'h46 || ascii == 8'h66 || ascii == 8'hC6 || ascii == 8'hE6)
    );

    // seg[6] matches the ASCII decode for segment g.
    check_seg_g_decode: assert property (
        @(posedge clk)
        seg[6] == (ascii == 8'h47 || ascii == 8'h67 || ascii == 8'hC7 || ascii == 8'hE7)
    );

    // seg[7] is asserted only for space.
    check_seg_space_decode: assert property (
        @(posedge clk)
        seg[7] == (ascii == 8'h20)
    );

    // The decoded segment outputs are mutually exclusive.
    check_segment_outputs_onehot0: assert property (
        @(posedge clk)
        $onehot0(seg[7:0])
    );

    // Unsupported ASCII values clear all defined segment outputs.
    check_unmapped_ascii_clears_segments: assert property (
        @(posedge clk)
        !(
            ascii == 8'h41 || ascii == 8'h61 || ascii == 8'hC1 || ascii == 8'hE1 ||
            ascii == 8'h42 || ascii == 8'h62 || ascii == 8'hC2 || ascii == 8'hE2 ||
            ascii == 8'h43 || ascii == 8'h63 || ascii == 8'hC3 || ascii == 8'hE3 ||
            ascii == 8'h44 || ascii == 8'h64 || ascii == 8'hC4 || ascii == 8'hE4 ||
            ascii == 8'h45 || ascii == 8'h65 || ascii == 8'hC5 || ascii == 8'hE5 ||
            ascii == 8'h46 || ascii == 8'h66 || ascii == 8'hC6 || ascii == 8'hE6 ||
            ascii == 8'h47 || ascii == 8'h67 || ascii == 8'hC7 || ascii == 8'hE7 ||
            ascii == 8'h20
        ) |-> (seg[7:0] == 8'b0000_0000)
    );

end
endgenerate

endmodule