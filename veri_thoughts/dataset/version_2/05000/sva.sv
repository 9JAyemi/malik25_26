module AregInexactSlice_sva (
    input logic [31:0] AM,
    input logic notAM31_3,
    input logic notAM2_0,
    input logic clk
);

    // No RTL clock or reset; clk is a sampling clock for this combinational DUT.

    // notAM31_3 matches the NAND of AM[31:19].
    check_notAM31_3_nand_equation: assert property (
        @(posedge clk) (notAM31_3 == ~(&AM[31:19]))
    );

    // All-high AM[31:19] drives notAM31_3 low.
    check_notAM31_3_all_high_drives_low: assert property (
        @(posedge clk) (&AM[31:19]) |-> (notAM31_3 == 1'b0)
    );

    // Any low bit in AM[31:19] drives notAM31_3 high.
    check_notAM31_3_any_low_drives_high: assert property (
        @(posedge clk) (~(&AM[31:19])) |-> (notAM31_3 == 1'b1)
    );

    // notAM2_0 matches the NAND of AM[2:0].
    check_notAM2_0_nand_equation: assert property (
        @(posedge clk) (notAM2_0 == ~(&AM[2:0]))
    );

    // All-high AM[2:0] drives notAM2_0 low.
    check_notAM2_0_all_high_drives_low: assert property (
        @(posedge clk) (&AM[2:0]) |-> (notAM2_0 == 1'b0)
    );

    // Any low bit in AM[2:0] drives notAM2_0 high.
    check_notAM2_0_any_low_drives_high: assert property (
        @(posedge clk) (~(&AM[2:0])) |-> (notAM2_0 == 1'b1)
    );

endmodule