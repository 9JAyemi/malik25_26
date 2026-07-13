module RoboticVehicleController_sva(
    input logic       DigitalLDir,
    input logic       DigitalRDir,
    input logic       reset_n,
    input logic [3:0] outputs
);

    // Active-low reset forces all outputs low.
    check_reset_forces_zero: assert property (
        @($global_clock)
        !reset_n |-> (outputs == 4'b0000)
    );

    // Upper output bits mirror the left direction input outside reset.
    check_upper_bits_follow_left: assert property (
        @($global_clock) disable iff (!reset_n)
        (outputs[3:2] == {2{DigitalLDir}})
    );

    // Lower output bits mirror the right direction input outside reset.
    check_lower_bits_follow_right: assert property (
        @($global_clock) disable iff (!reset_n)
        (outputs[1:0] == {2{DigitalRDir}})
    );

    // Both direction inputs high drive all outputs high.
    check_map_11_to_1111: assert property (
        @($global_clock) disable iff (!reset_n)
        ({DigitalLDir, DigitalRDir} == 2'b11) |-> (outputs == 4'b1111)
    );

    // Left high and right low drive only the upper outputs high.
    check_map_10_to_1100: assert property (
        @($global_clock) disable iff (!reset_n)
        ({DigitalLDir, DigitalRDir} == 2'b10) |-> (outputs == 4'b1100)
    );

    // Left low and right high drive only the lower outputs high.
    check_map_01_to_0011: assert property (
        @($global_clock) disable iff (!reset_n)
        ({DigitalLDir, DigitalRDir} == 2'b01) |-> (outputs == 4'b0011)
    );

    // Both direction inputs low drive all outputs low.
    check_map_00_to_0000: assert property (
        @($global_clock) disable iff (!reset_n)
        ({DigitalLDir, DigitalRDir} == 2'b00) |-> (outputs == 4'b0000)
    );

    // Outside reset, outputs always match the full combinational mapping.
    check_full_direction_mapping: assert property (
        @($global_clock) disable iff (!reset_n)
        (outputs == {DigitalLDir, DigitalLDir, DigitalRDir, DigitalRDir})
    );

endmodule