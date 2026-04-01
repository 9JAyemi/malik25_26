// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_regs, assert, property, h00, adder1_sum_definition, disable, iff, adder2_sum_definition, adder1_cout_definition, adder2_cout_definition, q_updates_on_select1, past, q_updates_on_select0, q1_captures_d1_on_select1, cin1_clears_on_select1, q2_captures_sum1_on_select1, cin2_captures_cout1_on_select1, q2_captures_d2_on_select0, cin2_clears_on_select0, q1_captures_sum2_on_select0, cin1_captures_cout2_on_select0
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d1(d1),
    .d2(d2),
    .select(select),
    .q(q),
    .q1(q1),
    .q2(q2),
    .cin1(cin1),
    .cin2(cin2),
    .sum1(sum1),
    .sum2(sum2),
    .cout1(cout1),
    .cout2(cout2),
    .posedge(posedge),
    .b0(b0)
);
