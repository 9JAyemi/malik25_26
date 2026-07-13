module top_module_sva(
    input logic         clk,
    input logic [255:0] in,
    input logic [7:0]   sel,
    input logic [31:0]  out
);

    function automatic logic [31:0] byte_reverse32(input logic [31:0] data);
        byte_reverse32 = {data[7:0], data[15:8], data[23:16], data[31:24]};
    endfunction

    // sel=8'hFF selects in[31:0], reverses its bytes, and adds the two values.
    check_sel_ff_selects_word0: assert property (
        @(posedge clk) (sel == 8'hFF) |-> (out == (in[31:0] + byte_reverse32(in[31:0])))
    );

    // sel=8'hFE selects in[63:32], reverses its bytes, and adds the two values.
    check_sel_fe_selects_word1: assert property (
        @(posedge clk) (sel == 8'hFE) |-> (out == (in[63:32] + byte_reverse32(in[63:32])))
    );

    // sel=8'hFD selects in[95:64], reverses its bytes, and adds the two values.
    check_sel_fd_selects_word2: assert property (
        @(posedge clk) (sel == 8'hFD) |-> (out == (in[95:64] + byte_reverse32(in[95:64])))
    );

    // sel=8'hFC selects in[127:96], reverses its bytes, and adds the two values.
    check_sel_fc_selects_word3: assert property (
        @(posedge clk) (sel == 8'hFC) |-> (out == (in[127:96] + byte_reverse32(in[127:96])))
    );

    // sel=8'hFB selects in[159:128], reverses its bytes, and adds the two values.
    check_sel_fb_selects_word4: assert property (
        @(posedge clk) (sel == 8'hFB) |-> (out == (in[159:128] + byte_reverse32(in[159:128])))
    );

    // sel=8'hFA selects in[191:160], reverses its bytes, and adds the two values.
    check_sel_fa_selects_word5: assert property (
        @(posedge clk) (sel == 8'hFA) |-> (out == (in[191:160] + byte_reverse32(in[191:160])))
    );

    // sel=8'hF9 selects in[223:192], reverses its bytes, and adds the two values.
    check_sel_f9_selects_word6: assert property (
        @(posedge clk) (sel == 8'hF9) |-> (out == (in[223:192] + byte_reverse32(in[223:192])))
    );

    // sel=8'hF8 selects in[255:224], reverses its bytes, and adds the two values.
    check_sel_f8_selects_word7: assert property (
        @(posedge clk) (sel == 8'hF8) |-> (out == (in[255:224] + byte_reverse32(in[255:224])))
    );

    // With a valid selection held constant, out depends only on the selected 32-bit word.
    check_out_stable_for_stable_valid_selection: assert property (
        @(posedge clk)
        (
            ((sel == 8'hFF) && $stable(sel) && $stable(in[31:0]))     ||
            ((sel == 8'hFE) && $stable(sel) && $stable(in[63:32]))    ||
            ((sel == 8'hFD) && $stable(sel) && $stable(in[95:64]))    ||
            ((sel == 8'hFC) && $stable(sel) && $stable(in[127:96]))   ||
            ((sel == 8'hFB) && $stable(sel) && $stable(in[159:128]))  ||
            ((sel == 8'hFA) && $stable(sel) && $stable(in[191:160]))  ||
            ((sel == 8'hF9) && $stable(sel) && $stable(in[223:192]))  ||
            ((sel == 8'hF8) && $stable(sel) && $stable(in[255:224]))
        ) |-> $stable(out)
    );

endmodule