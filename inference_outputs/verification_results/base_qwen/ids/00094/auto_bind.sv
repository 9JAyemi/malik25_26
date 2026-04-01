// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, rst_n, fa_0_s, fa_0_co, fa_1_s, fa_1_co, fa_2_s, fa_2_co, fa_3_s, fa_3_co, carry_out_correct, assert, property, posedge, disable, iff, sum_correct, fa_0_co_correct, fa_0_s_correct, fa_1_co_correct, fa_1_s_correct, fa_2_co_correct, fa_2_s_correct, fa_3_co_correct, fa_3_s_correct, reset_outputs_zero, b0, b0000
bind FullAdder RippleAdder2_sva auto_sva_inst (
    .a(a),
    .b(b),
    .ci(ci),
    .co(co),
    .s(s),
    .c(c),
    .FullAdder(FullAdder),
    .fa_0_inst(fa_0_inst),
    .fa_1_inst(fa_1_inst),
    .fa_2_inst(fa_2_inst),
    .fa_3_inst(fa_3_inst),
    .always(always),
    .begin(begin),
    .assig_process_c(assig_process_c),
    .end(end),
    .assig_process_co(assig_process_co),
    .assig_process_s(assig_process_s)
);
