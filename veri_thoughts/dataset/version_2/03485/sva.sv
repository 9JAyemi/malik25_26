module altera_up_av_config_auto_init_lcm_sva #(
    parameter [7:0] LCM_INPUT_FORMAT_UB               = 8'h00,
    parameter [7:0] LCM_INPUT_FORMAT_LB               = 8'h01,
    parameter [7:0] LCM_POWER                         = 8'h3F,
    parameter [7:0] LCM_DIRECTION_AND_PHASE           = 8'h17,
    parameter [7:0] LCM_HORIZONTAL_START_POSITION     = 8'h18,
    parameter [7:0] LCM_VERTICAL_START_POSITION       = 8'h08,
    parameter [7:0] LCM_ENB_NEGATIVE_POSITION         = 8'h00,
    parameter [7:0] LCM_GAIN_OF_CONTRAST              = 8'h20,
    parameter [7:0] LCM_R_GAIN_OF_SUB_CONTRAST        = 8'h20,
    parameter [7:0] LCM_B_GAIN_OF_SUB_CONTRAST        = 8'h20,
    parameter [7:0] LCM_OFFSET_OF_BRIGHTNESS          = 8'h10,
    parameter [7:0] LCM_VCOM_HIGH_LEVEL               = 8'h3F,
    parameter [7:0] LCM_VCOM_LOW_LEVEL                = 8'h3F,
    parameter [7:0] LCM_PCD_HIGH_LEVEL                = 8'h2F,
    parameter [7:0] LCM_PCD_LOW_LEVEL                 = 8'h2F,
    parameter [7:0] LCM_GAMMA_CORRECTION_0            = 8'h98,
    parameter [7:0] LCM_GAMMA_CORRECTION_1            = 8'h9A,
    parameter [7:0] LCM_GAMMA_CORRECTION_2            = 8'hA9,
    parameter [7:0] LCM_GAMMA_CORRECTION_3            = 8'h99,
    parameter [7:0] LCM_GAMMA_CORRECTION_4            = 8'h08
) (
    input  logic        clk,
    input  logic [4:0]  rom_address,
    input  logic [15:0] rom_data
);

    // Bits [9:8] are always zero in the formatted ROM word.
    check_rom_data_middle_bits_zero: assert property (
        @(posedge clk) rom_data[9:8] == 2'b00
    );

    // Address 0 returns the input format upper byte entry.
    check_rom_addr_0_entry: assert property (
        @(posedge clk) (rom_address == 5'd0) |-> (rom_data == {6'h02, 2'b00, LCM_INPUT_FORMAT_UB})
    );

    // Address 1 returns the input format lower byte entry.
    check_rom_addr_1_entry: assert property (
        @(posedge clk) (rom_address == 5'd1) |-> (rom_data == {6'h03, 2'b00, LCM_INPUT_FORMAT_LB})
    );

    // Address 2 returns the power entry.
    check_rom_addr_2_entry: assert property (
        @(posedge clk) (rom_address == 5'd2) |-> (rom_data == {6'h04, 2'b00, LCM_POWER})
    );

    // Address 3 returns the direction and phase entry.
    check_rom_addr_3_entry: assert property (
        @(posedge clk) (rom_address == 5'd3) |-> (rom_data == {6'h05, 2'b00, LCM_DIRECTION_AND_PHASE})
    );

    // Address 4 returns the horizontal start position entry.
    check_rom_addr_4_entry: assert property (
        @(posedge clk) (rom_address == 5'd4) |-> (rom_data == {6'h06, 2'b00, LCM_HORIZONTAL_START_POSITION})
    );

    // Address 5 returns the vertical start position entry.
    check_rom_addr_5_entry: assert property (
        @(posedge clk) (rom_address == 5'd5) |-> (rom_data == {6'h07, 2'b00, LCM_VERTICAL_START_POSITION})
    );

    // Address 6 returns the ENB negative position entry.
    check_rom_addr_6_entry: assert property (
        @(posedge clk) (rom_address == 5'd6) |-> (rom_data == {6'h08, 2'b00, LCM_ENB_NEGATIVE_POSITION})
    );

    // Address 7 returns the contrast gain entry.
    check_rom_addr_7_entry: assert property (
        @(posedge clk) (rom_address == 5'd7) |-> (rom_data == {6'h09, 2'b00, LCM_GAIN_OF_CONTRAST})
    );

    // Address 8 returns the red sub-contrast gain entry.
    check_rom_addr_8_entry: assert property (
        @(posedge clk) (rom_address == 5'd8) |-> (rom_data == {6'h0A, 2'b00, LCM_R_GAIN_OF_SUB_CONTRAST})
    );

    // Address 9 returns the blue sub-contrast gain entry.
    check_rom_addr_9_entry: assert property (
        @(posedge clk) (rom_address == 5'd9) |-> (rom_data == {6'h0B, 2'b00, LCM_B_GAIN_OF_SUB_CONTRAST})
    );

    // Address 10 returns the brightness offset entry.
    check_rom_addr_10_entry: assert property (
        @(posedge clk) (rom_address == 5'd10) |-> (rom_data == {6'h0C, 2'b00, LCM_OFFSET_OF_BRIGHTNESS})
    );

    // Address 11 returns the VCOM high level entry.
    check_rom_addr_11_entry: assert property (
        @(posedge clk) (rom_address == 5'd11) |-> (rom_data == {6'h10, 2'b00, LCM_VCOM_HIGH_LEVEL})
    );

    // Address 12 returns the VCOM low level entry.
    check_rom_addr_12_entry: assert property (
        @(posedge clk) (rom_address == 5'd12) |-> (rom_data == {6'h11, 2'b00, LCM_VCOM_LOW_LEVEL})
    );

    // Address 13 returns the PCD high level entry.
    check_rom_addr_13_entry: assert property (
        @(posedge clk) (rom_address == 5'd13) |-> (rom_data == {6'h12, 2'b00, LCM_PCD_HIGH_LEVEL})
    );

    // Address 14 returns the PCD low level entry.
    check_rom_addr_14_entry: assert property (
        @(posedge clk) (rom_address == 5'd14) |-> (rom_data == {6'h13, 2'b00, LCM_PCD_LOW_LEVEL})
    );

    // Address 15 returns the first gamma correction entry.
    check_rom_addr_15_entry: assert property (
        @(posedge clk) (rom_address == 5'd15) |-> (rom_data == {6'h14, 2'b00, LCM_GAMMA_CORRECTION_0})
    );

    // Address 16 returns the second gamma correction entry.
    check_rom_addr_16_entry: assert property (
        @(posedge clk) (rom_address == 5'd16) |-> (rom_data == {6'h15, 2'b00, LCM_GAMMA_CORRECTION_1})
    );

    // Address 17 returns the third gamma correction entry.
    check_rom_addr_17_entry: assert property (
        @(posedge clk) (rom_address == 5'd17) |-> (rom_data == {6'h16, 2'b00, LCM_GAMMA_CORRECTION_2})
    );

    // Address 18 returns the fourth gamma correction entry.
    check_rom_addr_18_entry: assert property (
        @(posedge clk) (rom_address == 5'd18) |-> (rom_data == {6'h17, 2'b00, LCM_GAMMA_CORRECTION_3})
    );

    // Address 19 returns the fifth gamma correction entry.
    check_rom_addr_19_entry: assert property (
        @(posedge clk) (rom_address == 5'd19) |-> (rom_data == {6'h18, 2'b00, LCM_GAMMA_CORRECTION_4})
    );

    // Addresses outside 0 to 19 return zero.
    check_rom_default_entry: assert property (
        @(posedge clk) (rom_address > 5'd19) |-> (rom_data == 16'h0000)
    );

endmodule