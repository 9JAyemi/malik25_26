module decoder_4to16_sva (
    input logic         clk,
    input logic [255:0] in,
    input logic [3:0]   sel,
    input logic [15:0]  out
);

    // sel=0 maps to bit 0.
    check_decode_sel_0: assert property (
        @(posedge clk) (sel == 4'h0) |-> (out == 16'h0001)
    );

    // sel=1 maps to bit 1.
    check_decode_sel_1: assert property (
        @(posedge clk) (sel == 4'h1) |-> (out == 16'h0002)
    );

    // sel=2 maps to bit 2.
    check_decode_sel_2: assert property (
        @(posedge clk) (sel == 4'h2) |-> (out == 16'h0004)
    );

    // sel=3 maps to bit 3.
    check_decode_sel_3: assert property (
        @(posedge clk) (sel == 4'h3) |-> (out == 16'h0008)
    );

    // sel=4 maps to bit 4.
    check_decode_sel_4: assert property (
        @(posedge clk) (sel == 4'h4) |-> (out == 16'h0010)
    );

    // sel=5 maps to bit 5.
    check_decode_sel_5: assert property (
        @(posedge clk) (sel == 4'h5) |-> (out == 16'h0020)
    );

    // sel=6 maps to bit 6.
    check_decode_sel_6: assert property (
        @(posedge clk) (sel == 4'h6) |-> (out == 16'h0040)
    );

    // sel=7 maps to bit 7.
    check_decode_sel_7: assert property (
        @(posedge clk) (sel == 4'h7) |-> (out == 16'h0080)
    );

    // sel=8 maps to bit 8.
    check_decode_sel_8: assert property (
        @(posedge clk) (sel == 4'h8) |-> (out == 16'h0100)
    );

    // sel=9 maps to bit 9.
    check_decode_sel_9: assert property (
        @(posedge clk) (sel == 4'h9) |-> (out == 16'h0200)
    );

    // sel=10 maps to bit 10.
    check_decode_sel_a: assert property (
        @(posedge clk) (sel == 4'hA) |-> (out == 16'h0400)
    );

    // sel=11 maps to bit 11.
    check_decode_sel_b: assert property (
        @(posedge clk) (sel == 4'hB) |-> (out == 16'h0800)
    );

    // sel=12 maps to bit 12.
    check_decode_sel_c: assert property (
        @(posedge clk) (sel == 4'hC) |-> (out == 16'h1000)
    );

    // sel=13 maps to bit 13.
    check_decode_sel_d: assert property (
        @(posedge clk) (sel == 4'hD) |-> (out == 16'h2000)
    );

    // sel=14 maps to bit 14.
    check_decode_sel_e: assert property (
        @(posedge clk) (sel == 4'hE) |-> (out == 16'h4000)
    );

    // sel=15 maps to bit 15.
    check_decode_sel_f: assert property (
        @(posedge clk) (sel == 4'hF) |-> (out == 16'h8000)
    );

    // Unknown select values drive the default zero output.
    check_unknown_sel_default_zero: assert property (
        @(posedge clk) $isunknown(sel) |-> (out == 16'h0000)
    );

    // Output is always one-hot or all zero.
    check_out_onehot0: assert property (
        @(posedge clk) $onehot0(out)
    );

    // Holding sel constant holds out constant.
    check_sel_stable_implies_out_stable: assert property (
        @(posedge clk) $stable(sel) |-> $stable(out)
    );

    // Changing in alone does not affect out.
    check_in_change_no_effect: assert property (
        @(posedge clk) $changed(in) && $stable(sel) |-> $stable(out)
    );

endmodule