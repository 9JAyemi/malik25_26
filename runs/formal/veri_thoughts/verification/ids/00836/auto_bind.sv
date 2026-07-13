// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_rsp_valid_mirror, assert, property, posedge, disable, iff, check_cmd_ready_mirror, mux_select0_routes_in0, mux_select1_routes_in1, mux_function_equivalence, out_stable_when_inputs_stable, stable, upper_id_bits_no_effect, past, edge_rise_valid_mirror, rose, edge_fall_valid_mirror, fell, edge_rise_ready_mirror, edge_fall_ready_mirror
bind Cfu Cfu_sva auto_sva_inst (
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_payload_function_id(cmd_payload_function_id),
    .cmd_payload_inputs_0(cmd_payload_inputs_0),
    .cmd_payload_inputs_1(cmd_payload_inputs_1),
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_payload_outputs_0(rsp_payload_outputs_0),
    .reset(reset),
    .clk(clk)
);
