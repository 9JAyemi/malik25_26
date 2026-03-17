// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_irq_definition, assert, property, disable, iff, check_data_out_on_read, check_data_out_when_not_read, h00, reset_clears_icrmask, b0_00000, reset_clears_icr, write_sets_mask_bits, b1, past, write_clears_mask_bits, b0, icrmask_holds_without_write, regs_hold_when_clk7_en_low, icr_captures_inputs_on_read, icr_or_latches_when_not_read
bind interrupt_controller interrupt_controller_sva auto_sva_inst (
    .clk(clk),
    .clk7_en(clk7_en),
    .wr(wr),
    .reset(reset),
    .icrs(icrs),
    .ta(ta),
    .tb(tb),
    .alrm(alrm),
    .flag(flag),
    .ser(ser),
    .data_in(data_in),
    .data_out(data_out),
    .irq(irq),
    .icr(icr),
    .icrmask(icrmask),
    .posedge(posedge),
    .b00(b00)
);
