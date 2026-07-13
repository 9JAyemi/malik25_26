module Chip_Decoder_sva(
    input logic clk,
    input logic A9,
    input logic A8,
    input logic F,
    input logic A3,
    input logic A2,
    input logic AEN,
    input logic IORbar,
    input logic IOWbar,
    input logic [3:0] CSbar,
    input logic Ebar,
    input logic DIR
);

    // Ebar is low only for the qualified decoded I/O access condition.
    check_ebar_low_on_qualified_access: assert property (
        @(posedge clk)
        ((A9 == 1'b1) & (A8 == 1'b1) & (AEN == 1'b0) & (F == 1'b1) & (IORbar != IOWbar)) |-> (Ebar == 1'b0)
    );

    // Ebar is high whenever the qualified decoded I/O access condition is false.
    check_ebar_high_without_qualified_access: assert property (
        @(posedge clk)
        !((A9 == 1'b1) & (A8 == 1'b1) & (AEN == 1'b0) & (F == 1'b1) & (IORbar != IOWbar)) |-> (Ebar == 1'b1)
    );

    // DIR is low only during an I/O read cycle.
    check_dir_low_on_read_cycle: assert property (
        @(posedge clk)
        ((IORbar == 1'b0) & (IOWbar == 1'b1)) |-> (DIR == 1'b0)
    );

    // DIR is high for all non-read combinations of IORbar and IOWbar.
    check_dir_high_otherwise: assert property (
        @(posedge clk)
        !((IORbar == 1'b0) & (IOWbar == 1'b1)) |-> (DIR == 1'b1)
    );

    // Address 00 selects CSbar[0] active low.
    check_csbar_decode_00: assert property (
        @(posedge clk)
        ((A3 == 1'b0) & (A2 == 1'b0)) |-> (CSbar == 4'b1110)
    );

    // Address 01 selects CSbar[1] active low.
    check_csbar_decode_01: assert property (
        @(posedge clk)
        ((A3 == 1'b0) & (A2 == 1'b1)) |-> (CSbar == 4'b1101)
    );

    // Address 10 selects CSbar[2] active low.
    check_csbar_decode_10: assert property (
        @(posedge clk)
        ((A3 == 1'b1) & (A2 == 1'b0)) |-> (CSbar == 4'b1011)
    );

    // Address 11 selects CSbar[3] active low.
    check_csbar_decode_11: assert property (
        @(posedge clk)
        ((A3 == 1'b1) & (A2 == 1'b1)) |-> (CSbar == 4'b0111)
    );

    // CSbar always has exactly one active-low chip select.
    check_csbar_one_active_low: assert property (
        @(posedge clk)
        $onehot(~CSbar)
    );

endmodule