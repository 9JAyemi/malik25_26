module Video_System_CPU_nios2_oci_td_mode_sva (
    input logic clk,
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);

// td_mode matches the RTL case mapping of ctrl[7:5].
    check_td_mode_mapping: assert property (
        @(posedge clk)
        td_mode == ((ctrl[7:5] == 3'b000) ? 4'b0000 :
                    (ctrl[7:5] == 3'b001) ? 4'b1000 :
                    (ctrl[7:5] == 3'b010) ? 4'b0100 :
                    (ctrl[7:5] == 3'b011) ? 4'b1100 :
                    (ctrl[7:5] == 3'b100) ? 4'b0010 :
                    (ctrl[7:5] == 3'b101) ? 4'b1010 :
                    (ctrl[7:5] == 3'b110) ? 4'b0101 :
                                             4'b1111)
    );

// ctrl[7:5]==000 selects 0000.
    check_ctrl_000_maps_to_0000: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b000) |-> (td_mode == 4'b0000)
    );

// ctrl[7:5]==001 selects 1000.
    check_ctrl_001_maps_to_1000: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b001) |-> (td_mode == 4'b1000)
    );

// ctrl[7:5]==010 selects 0100.
    check_ctrl_010_maps_to_0100: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b010) |-> (td_mode == 4'b0100)
    );

// ctrl[7:5]==011 selects 1100.
    check_ctrl_011_maps_to_1100: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b011) |-> (td_mode == 4'b1100)
    );

// ctrl[7:5]==100 selects 0010.
    check_ctrl_100_maps_to_0010: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b100) |-> (td_mode == 4'b0010)
    );

// ctrl[7:5]==101 selects 1010.
    check_ctrl_101_maps_to_1010: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b101) |-> (td_mode == 4'b1010)
    );

// ctrl[7:5]==110 selects 0101.
    check_ctrl_110_maps_to_0101: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b110) |-> (td_mode == 4'b0101)
    );

// ctrl[7:5]==111 selects 1111.
    check_ctrl_111_maps_to_1111: assert property (
        @(posedge clk)
        (ctrl[7:5] == 3'b111) |-> (td_mode == 4'b1111)
    );

// Any unmapped ctrl[7:5] value selects 1111.
    check_default_maps_to_1111: assert property (
        @(posedge clk)
        ((ctrl[7:5] != 3'b000) &&
         (ctrl[7:5] != 3'b001) &&
         (ctrl[7:5] != 3'b010) &&
         (ctrl[7:5] != 3'b011) &&
         (ctrl[7:5] != 3'b100) &&
         (ctrl[7:5] != 3'b101) &&
         (ctrl[7:5] != 3'b110)) |-> (td_mode == 4'b1111)
    );

endmodule
