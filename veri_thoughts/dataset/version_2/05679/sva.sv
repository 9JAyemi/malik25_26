module td_mode_module_sva (
    input logic        clk,
    input logic [8:0]  ctrl,
    input logic [3:0]  td_mode
);

    // 000 selects td_mode 0000.
    check_td_mode_decode_000: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b000) |-> (td_mode == 4'b0000)
    );

    // 001 selects td_mode 1000.
    check_td_mode_decode_001: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b001) |-> (td_mode == 4'b1000)
    );

    // 010 selects td_mode 0100.
    check_td_mode_decode_010: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b010) |-> (td_mode == 4'b0100)
    );

    // 011 selects td_mode 1100.
    check_td_mode_decode_011: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b011) |-> (td_mode == 4'b1100)
    );

    // 100 selects td_mode 0010.
    check_td_mode_decode_100: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b100) |-> (td_mode == 4'b0010)
    );

    // 101 selects td_mode 1010.
    check_td_mode_decode_101: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b101) |-> (td_mode == 4'b1010)
    );

    // 110 selects td_mode 0101.
    check_td_mode_decode_110: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b110) |-> (td_mode == 4'b0101)
    );

    // 111 selects td_mode 1111.
    check_td_mode_decode_111: assert property (
        @(posedge clk) (ctrl[7:5] == 3'b111) |-> (td_mode == 4'b1111)
    );

endmodule