module synchronizer_sva (
    input logic clk,
    input logic rst,
    input logic sensor,
    input logic reprogram,
    input logic walk_btn,
    input logic rst_out,
    input logic sensor_out,
    input logic walk_register,
    input logic reprogram_out
);

    // rst_out is a 1-cycle registered copy of rst.
    check_reg_copy_rst: assert property (
        @(posedge clk) disable iff ($initstate) rst_out == $past(rst)
    );

    // sensor_out is a 1-cycle registered copy of sensor.
    check_reg_copy_sensor: assert property (
        @(posedge clk) disable iff ($initstate) sensor_out == $past(sensor)
    );

    // walk_register is a 1-cycle registered copy of walk_btn.
    check_reg_copy_walk: assert property (
        @(posedge clk) disable iff ($initstate) walk_register == $past(walk_btn)
    );

    // reprogram_out is a 1-cycle registered copy of reprogram.
    check_reg_copy_reprogram: assert property (
        @(posedge clk) disable iff ($initstate) reprogram_out == $past(reprogram)
    );

    // A change on rst causes rst_out to change on the next cycle.
    check_change_propagation_rst: assert property (
        @(posedge clk) disable iff ($initstate) $changed(rst) |-> ##1 $changed(rst_out)
    );

    // A change on sensor causes sensor_out to change on the next cycle.
    check_change_propagation_sensor: assert property (
        @(posedge clk) disable iff ($initstate) $changed(sensor) |-> ##1 $changed(sensor_out)
    );

    // A change on walk_btn causes walk_register to change on the next cycle.
    check_change_propagation_walk: assert property (
        @(posedge clk) disable iff ($initstate) $changed(walk_btn) |-> ##1 $changed(walk_register)
    );

    // A change on reprogram causes reprogram_out to change on the next cycle.
    check_change_propagation_reprogram: assert property (
        @(posedge clk) disable iff ($initstate) $changed(reprogram) |-> ##1 $changed(reprogram_out)
    );

    // If rst is stable across a cycle, rst_out remains stable in the following cycle.
    check_stability_follow_rst: assert property (
        @(posedge clk) disable iff ($initstate) $stable(rst) |-> ##1 $stable(rst_out)
    );

    // If sensor is stable across a cycle, sensor_out remains stable in the following cycle.
    check_stability_follow_sensor: assert property (
        @(posedge clk) disable iff ($initstate) $stable(sensor) |-> ##1 $stable(sensor_out)
    );

    // If walk_btn is stable across a cycle, walk_register remains stable in the following cycle.
    check_stability_follow_walk: assert property (
        @(posedge clk) disable iff ($initstate) $stable(walk_btn) |-> ##1 $stable(walk_register)
    );

    // If reprogram is stable across a cycle, reprogram_out remains stable in the following cycle.
    check_stability_follow_reprogram: assert property (
        @(posedge clk) disable iff ($initstate) $stable(reprogram) |-> ##1 $stable(reprogram_out)
    );

endmodule