module top_sva (
    input logic        clk,
    input logic [31:0] incom,
    input logic [31:0] outgo
);

    // The 32-bit output is always the bitwise inverse of the 32-bit input.
    check_full_inversion: assert property (
        @(posedge clk) outgo == ~incom
    );

    // BT0 inverts the low byte.
    check_bt0_inversion: assert property (
        @(posedge clk) outgo[7:0] == ~incom[7:0]
    );

    // BT1 inverts bits [15:8].
    check_bt1_inversion: assert property (
        @(posedge clk) outgo[15:8] == ~incom[15:8]
    );

    // BT2 inverts bits [23:16].
    check_bt2_inversion: assert property (
        @(posedge clk) outgo[23:16] == ~incom[23:16]
    );

    // BT3 inverts the high byte.
    check_bt3_inversion: assert property (
        @(posedge clk) outgo[31:24] == ~incom[31:24]
    );

endmodule