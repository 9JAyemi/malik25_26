// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_sum_zero_on_clear, assert, property, check_q1_loads_d1, disable, iff, past, check_q1_shifts_left, check_q2_loads_q1, check_q2_shifts_left, check_sum_equals_q1_plus_q2, b1, check_q2_loads_d1_when_both_loads_high, check_q2_shifts_left_when_both_loads_low
bind shift_register top_module_sva auto_sva_inst (
    .D1(D1),
    .D2(D2),
    .LD1(LD1),
    .LD2(LD2),
    .CLK(CLK),
    .CLR(CLR),
    .sum(sum),
    .posedge(posedge),
    .b0000(b0000),
    .Q1(Q1),
    .Q2(Q2)
);
