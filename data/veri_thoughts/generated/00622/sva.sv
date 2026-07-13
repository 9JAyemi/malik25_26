module td_mode_generator_sva (
    input logic clk,              // External clock for SVA sampling (RTL is combinational)
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);
    ///// Combinational decode mapping checks /////
    // When ctrl[8:6]==000, td_mode must be 0000.
    check_decode_000: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b000) |-> (td_mode == 4'b0000)
    );
    // When ctrl[8:6]==001, td_mode must be 1000.
    check_decode_001: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b001) |-> (td_mode == 4'b1000)
    );
    // When ctrl[8:6]==010, td_mode must be 0100.
    check_decode_010: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b010) |-> (td_mode == 4'b0100)
    );
    // When ctrl[8:6]==011, td_mode must be 1100.
    check_decode_011: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b011) |-> (td_mode == 4'b1100)
    );
    // When ctrl[8:6]==100, td_mode must be 0010.
    check_decode_100: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b100) |-> (td_mode == 4'b0010)
    );
    // When ctrl[8:6]==101, td_mode must be 1010.
    check_decode_101: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b101) |-> (td_mode == 4'b1010)
    );
    // When ctrl[8:6]==110, td_mode must be 0101.
    check_decode_110: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b110) |-> (td_mode == 4'b0101)
    );
    // When ctrl[8:6]==111, td_mode must be 1111.
    check_decode_111: assert property (
        @(posedge clk) disable iff (1'b0) (ctrl[8:6] == 3'b111) |-> (td_mode == 4'b1111)
    );

    ///// Output value constraints /////
    // td_mode must always be one of the defined decode values.
    check_td_mode_value_set: assert property (
        @(posedge clk) disable iff (1'b0) td_mode inside {4'b0000,4'b1000,4'b0100,4'b1100,4'b0010,4'b1010,4'b0101,4'b1111}
    );

    ///// Dependency and stability checks /////
    // Changes in ctrl[8:6] must cause a change in td_mode (unique mapping).
    check_output_changes_with_key_input: assert property (
        @(posedge clk) disable iff (1'b0) $changed(ctrl[8:6]) |-> $changed(td_mode)
    );
    // td_mode may only change when ctrl[8:6] changes.
    check_no_spurious_output_change: assert property (
        @(posedge clk) disable iff (1'b0) $changed(td_mode) |-> $changed(ctrl[8:6])
    );
    // Changes in lower ctrl bits [5:0] alone must not change td_mode.
    check_lower_bits_irrelevant: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(ctrl[5:0]) && !$changed(ctrl[8:6])) |-> !$changed(td_mode)
    );
endmodule