// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reg_copy_rst, assert, property, posedge, disable, iff, initstate, past, check_reg_copy_sensor, check_reg_copy_walk, check_reg_copy_reprogram, check_change_propagation_rst, changed, check_change_propagation_sensor, check_change_propagation_walk, check_change_propagation_reprogram, check_stability_follow_rst, stable, check_stability_follow_sensor, check_stability_follow_walk, check_stability_follow_reprogram
bind synchronizer synchronizer_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .sensor(sensor),
    .reprogram(reprogram),
    .walk_btn(walk_btn),
    .rst_out(rst_out),
    .sensor_out(sensor_out),
    .walk_register(walk_register),
    .reprogram_out(reprogram_out)
);
