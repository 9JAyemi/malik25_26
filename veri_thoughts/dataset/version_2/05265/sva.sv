module BROM_sva(
    input logic [7:1]  adr_i,
    input logic        stb_i,
    input logic        ack_o,
    input logic [15:0] dat_o,
    input logic        clk
);

    // ack_o is a direct copy of stb_i.
    check_ack_matches_stb: assert property (
        @(posedge clk) disable iff (1'b0)
        (ack_o == stb_i)
    );

    // Address 0 and 4 return 16'h0113.
    check_data_addr_0_or_4: assert property (
        @(posedge clk) disable iff (1'b0)
        ((adr_i == 7'd0) || (adr_i == 7'd4)) |-> (dat_o == 16'h0113)
    );

    // Address 1 returns 16'h0000.
    check_data_addr_1: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd1) |-> (dat_o == 16'h0000)
    );

    // Address 2 returns 16'h01B7.
    check_data_addr_2: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd2) |-> (dat_o == 16'h01B7)
    );

    // Address 3 returns 16'h0010.
    check_data_addr_3: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd3) |-> (dat_o == 16'h0010)
    );

    // Address 5 and 7 return 16'h0011.
    check_data_addr_5_or_7: assert property (
        @(posedge clk) disable iff (1'b0)
        ((adr_i == 7'd5) || (adr_i == 7'd7)) |-> (dat_o == 16'h0011)
    );

    // Address 6 returns 16'h5213.
    check_data_addr_6: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd6) |-> (dat_o == 16'h5213)
    );

    // Address 8 returns 16'h9123.
    check_data_addr_8: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd8) |-> (dat_o == 16'h9123)
    );

    // Address 9 returns 16'h0041.
    check_data_addr_9: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd9) |-> (dat_o == 16'h0041)
    );

    // Address 10 returns 16'hF06F.
    check_data_addr_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd10) |-> (dat_o == 16'hF06F)
    );

    // Address 11 returns 16'hFF5F.
    check_data_addr_11: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i == 7'd11) |-> (dat_o == 16'hFF5F)
    );

    // Addresses 12 through 127 return 16'hCCCC.
    check_data_addr_12_to_127: assert property (
        @(posedge clk) disable iff (1'b0)
        (adr_i >= 7'd12) |-> (dat_o == 16'hCCCC)
    );

endmodule