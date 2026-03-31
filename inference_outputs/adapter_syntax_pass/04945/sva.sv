module Span12Mux_s5_v_sva (
    input logic clk,
    input logic [11:0] I,
    input logic O
);

    // O is high only for I equal to 12'h001.
    check_o_high_only_for_001: assert property (
        @(posedge clk) O |-> (I == 12'h001)
    );

    // I equal to 12'h001 drives O high.
    check_001_drives_o_high: assert property (
        @(posedge clk) (I == 12'h001) |-> (O == 1'b1)
    );

    // I equal to 12'h002 drives O low.
    check_002_drives_o_low: assert property (
        @(posedge clk) (I == 12'h002) |-> (O == 1'b0)
    );

    // I equal to 12'h004 drives O high.
    check_004_drives_o_high: assert property (
        @(posedge clk) (I == 12'h004) |-> (O == 1'b1)
    );

    // I equal to 12'h008 drives O low.
    check_008_drives_o_low: assert property (
        @(posedge clk) (I == 12'h008) |-> (O == 1'b0)
    );

    // I equal to 12'h010 drives O high.
    check_010_drives_o_high: assert property (
        @(posedge clk) (I == 12'h010) |-> (O == 1'b1)
    );

    // I equal to 12'h020 drives O low.
    check_020_drives_o_low: assert property (
        @(posedge clk) (I == 12'h020) |-> (O == 1'b0)
    );

    // I equal to 12'h040 drives O high.
    check_040_drives_o_high: assert property (
        @(posedge clk) (I == 12'h040) |-> (O == 1'b1)
    );

    // I equal to 12'h080 drives O low.
    check_080_drives_o_low: assert property (
        @(posedge clk) (I == 12'h080) |-> (O == 1'b0)
    );

    // I equal to 12'h100 drives O high.
    check_100_drives_o_high: assert property (
        @(posedge clk) (I == 12'h100) |-> (O == 1'b1)
    );

    // I equal to 12'h200 drives O low.
    check_200_drives_o_low: assert property (
        @(posedge clk) (I == 12'h200) |-> (O == 1'b0)
    );

    // I equal to 12'h400 drives O high.
    check_400_drives_o_high: assert property (
        @(posedge clk) (I == 12'h400) |-> (O == 1'b1)
    );

    // I equal to 12'h800 drives O low.
    check_800_drives_o_low: assert property (
        @(posedge clk) (I == 12'h800) |-> (O == 1'b0)
    );

    // I equal to 12'h000 drives O low.
    check_000_drives_o_low: assert property (
        @(posedge clk) (I == 12'h000) |-> (O == 1'b0)
    );

    // I equal to 12'hFFF drives O low.
    check_fff_drives_o_low: assert property (
        @(posedge clk) (I == 12'hFFF) |-> (O == 1'b0)
    );

endmodule