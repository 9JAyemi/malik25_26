module Video_System_CPU_nios2_oci_td_mode_sva (
    input logic        clk,
    input logic [8:0]  ctrl,
    input logic [3:0]  td_mode
);

    // ctrl[7:5] 000 maps to td_mode 0000.
    check_ctrl_000_maps_td_0000: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b000) |-> (td_mode == 4'b0000)
    );

    // ctrl[7:5] 001 maps to td_mode 1000.
    check_ctrl_001_maps_td_1000: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b001) |-> (td_mode == 4'b1000)
    );

    // ctrl[7:5] 010 maps to td_mode 0100.
    check_ctrl_010_maps_td_0100: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b010) |-> (td_mode == 4'b0100)
    );

    // ctrl[7:5] 011 maps to td_mode 1100.
    check_ctrl_011_maps_td_1100: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b011) |-> (td_mode == 4'b1100)
    );

    // ctrl[7:5] 100 maps to td_mode 0010.
    check_ctrl_100_maps_td_0010: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b100) |-> (td_mode == 4'b0010)
    );

    // ctrl[7:5] 101 maps to td_mode 1010.
    check_ctrl_101_maps_td_1010: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b101) |-> (td_mode == 4'b1010)
    );

    // ctrl[7:5] 110 maps to td_mode 0101.
    check_ctrl_110_maps_td_0101: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b110) |-> (td_mode == 4'b0101)
    );

    // ctrl[7:5] 111 maps to td_mode 1111.
    check_ctrl_111_maps_td_1111: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b111) |-> (td_mode == 4'b1111)
    );

    // Any unmapped ctrl[7:5] value uses the default 0000 mapping.
    check_default_maps_td_0000: assert property (
        @(posedge clk)
        ((ctrl[7:5] != 3'b000) &&
         (ctrl[7:5] != 3'b001) &&
         (ctrl[7:5] != 3'b010) &&
         (ctrl[7:5] != 3'b011) &&
         (ctrl[7:5] != 3'b100) &&
         (ctrl[7:5] != 3'b101) &&
         (ctrl[7:5] != 3'b110) &&
         (ctrl[7:5] != 3'b111))
        |-> (td_mode == 4'b0000)
    );

endmodule