module wasca_nios2_gen2_0_cpu_nios2_oci_td_mode_sva (
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);

    // ctrl 0 selects no trace.
    check_ctrl_0_maps_no_trace: assert property (
        @($global_clock) (ctrl == 9'b000000000) |-> (td_mode == 4'b0000)
    );

    // ctrl 1 selects record load address.
    check_ctrl_1_maps_load_address: assert property (
        @($global_clock) (ctrl == 9'b000000001) |-> (td_mode == 4'b0001)
    );

    // ctrl 2 selects record store address.
    check_ctrl_2_maps_store_address: assert property (
        @($global_clock) (ctrl == 9'b000000010) |-> (td_mode == 4'b0010)
    );

    // ctrl 3 selects record load data.
    check_ctrl_3_maps_load_data: assert property (
        @($global_clock) (ctrl == 9'b000000011) |-> (td_mode == 4'b0011)
    );

    // ctrl 4 selects record store data.
    check_ctrl_4_maps_store_data: assert property (
        @($global_clock) (ctrl == 9'b000000100) |-> (td_mode == 4'b0100)
    );

    // All other ctrl values select no trace.
    check_other_ctrl_values_map_no_trace: assert property (
        @($global_clock)
        !((ctrl == 9'b000000000) ||
          (ctrl == 9'b000000001) ||
          (ctrl == 9'b000000010) ||
          (ctrl == 9'b000000011) ||
          (ctrl == 9'b000000100))
        |-> (td_mode == 4'b0000)
    );

    // td_mode 1 only comes from ctrl 1.
    check_td_mode_1_has_unique_ctrl: assert property (
        @($global_clock) (td_mode == 4'b0001) |-> (ctrl == 9'b000000001)
    );

    // td_mode 2 only comes from ctrl 2.
    check_td_mode_2_has_unique_ctrl: assert property (
        @($global_clock) (td_mode == 4'b0010) |-> (ctrl == 9'b000000010)
    );

    // td_mode 3 only comes from ctrl 3.
    check_td_mode_3_has_unique_ctrl: assert property (
        @($global_clock) (td_mode == 4'b0011) |-> (ctrl == 9'b000000011)
    );

    // td_mode 4 only comes from ctrl 4.
    check_td_mode_4_has_unique_ctrl: assert property (
        @($global_clock) (td_mode == 4'b0100) |-> (ctrl == 9'b000000100)
    );

    // td_mode 0 only occurs when ctrl is not 1 through 4.
    check_td_mode_0_excludes_nonzero_modes: assert property (
        @($global_clock)
        (td_mode == 4'b0000)
        |-> !((ctrl == 9'b000000001) ||
              (ctrl == 9'b000000010) ||
              (ctrl == 9'b000000011) ||
              (ctrl == 9'b000000100))
    );

endmodule