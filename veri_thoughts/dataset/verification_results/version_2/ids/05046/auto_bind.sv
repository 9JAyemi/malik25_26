// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_majority_gate_logic, assert, property, disable, iff, check_counter_out_even_odd_select, check_counter_out_even_even_select, check_counter_reset_value, d0, check_final_output_reset_value, check_counter_increment_when_enabled, past, d1, check_counter_holds_when_disabled, check_final_output_holds_when_disabled, check_final_output_loads_counter_on_odd_count, b0000, check_final_output_loads_majority_on_even_count, b0000000
bind majority_counter majority_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .A(A),
    .B(B),
    .C(C),
    .D(D),
    .final_output(final_output),
    .Y(Y),
    .counter_out(counter_out),
    .counter_out_even(counter_out_even),
    .posedge(posedge)
);
