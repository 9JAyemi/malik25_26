module Video_System_CPU_nios2_oci_td_mode_sva (
    input logic clk,
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);
    ///// Mapping from ctrl[7:5] to td_mode /////
    // When ctrl[7:5]==3'b000, td_mode must be 4'b0000.
    check_map_000: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b000) |-> (td_mode == 4'b0000)
    );
    // When ctrl[7:5]==3'b001, td_mode must be 4'b1000.
    check_map_001: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b001) |-> (td_mode == 4'b1000)
    );
    // When ctrl[7:5]==3'b010, td_mode must be 4'b0100.
    check_map_010: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b010) |-> (td_mode == 4'b0100)
    );
    // When ctrl[7:5]==3'b011, td_mode must be 4'b1100.
    check_map_011: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b011) |-> (td_mode == 4'b1100)
    );
    // When ctrl[7:5]==3'b100, td_mode must be 4'b0010.
    check_map_100: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b100) |-> (td_mode == 4'b0010)
    );
    // When ctrl[7:5]==3'b101, td_mode must be 4'b1010.
    check_map_101: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b101) |-> (td_mode == 4'b1010)
    );
    // When ctrl[7:5]==3'b110, td_mode must be 4'b0101.
    check_map_110: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b110) |-> (td_mode == 4'b0101)
    );
    // When ctrl[7:5]==3'b111, td_mode must be 4'b1111.
    check_map_111: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b111) |-> (td_mode == 4'b1111)
    );

    ///// General invariants derived from the mapping /////
    // td_mode must always be one of the defined codewords.
    check_td_mode_code_set: assert property (
        @(posedge clk) td_mode inside {4'b0000,4'b1000,4'b0100,4'b1100,4'b0010,4'b1010,4'b0101,4'b1111}
    );
    // If ctrl[7:5] is stable, td_mode must be stable.
    check_stable_when_msb_stable: assert property (
        @(posedge clk) (ctrl[7:5] == $past(ctrl[7:5])) |-> (td_mode == $past(td_mode))
    );
    // Changes in ctrl[4:0] alone do not change td_mode.
    check_ignore_low_bits: assert property (
        @(posedge clk) (ctrl[7:5] == $past(ctrl[7:5]) && ctrl[4:0] != $past(ctrl[4:0])) |-> (td_mode == $past(td_mode))
    );
    // Changes in ctrl[8] alone do not change td_mode.
    check_ignore_bit8: assert property (
        @(posedge clk) (ctrl[7:5] == $past(ctrl[7:5]) && ctrl[8] != $past(ctrl[8])) |-> (td_mode == $past(td_mode))
    );
    // Any change in ctrl[7:5] must change td_mode (mapping is injective).
    check_ctrl_change_implies_td_change: assert property (
        @(posedge clk) (ctrl[7:5] != $past(ctrl[7:5])) |-> (td_mode != $past(td_mode))
    );
    // Any change in td_mode implies ctrl[7:5] changed.
    check_td_change_implies_ctrl_change: assert property (
        @(posedge clk) (td_mode != $past(td_mode)) |-> (ctrl[7:5] != $past(ctrl[7:5]))
    );
endmodule