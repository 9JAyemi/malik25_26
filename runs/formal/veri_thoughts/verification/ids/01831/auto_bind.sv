// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shifted_expected, always_comb, unique, reset_shift_00, assert, property, reset_shift_01, reset_shift_10, reset_shift_11, hold_when_load_and_inputs_stable, disable, iff, stable, past, inc_when_up_inputs_stable, d1, dec_when_down_inputs_stable, bounded_step_with_inputs_stable, wrap_increment_from_max, hF, h0, wrap_decrement_from_min
bind barrel_shifter top_module_sva auto_sva_inst (
    .clk(clk),
    .up_down(up_down),
    .load(load),
    .reset(reset),
    .data(data),
    .shift_amount(shift_amount),
    .Q(Q),
    .begin(begin),
    .case(case),
    .b00(b00),
    .b01(b01),
    .b10(b10),
    .b11(b11),
    .endcase(endcase),
    .end(end),
    .posedge(posedge)
);
