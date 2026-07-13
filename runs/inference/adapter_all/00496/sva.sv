module nonblocking_gate_sva (
    input logic        clk,
    input logic [4:0]  ctrl,
    input logic [1:0]  din,
    input logic [0:0]  sel,
    input logic [31:0] dout
);

    // dout increments by one on each clock.
    check_dout_increments: assert property (
        @(posedge clk) 1'b1 |=> (dout == ($past(dout) + 32'd1))
    );

    // When ctrl*sel is 0, dout[31:0] loads din.
    check_load_full_word: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd0) |=> (dout[31:0] == $past(din))
    );

    // When ctrl*sel is 1, dout[31:1] loads din.
    check_load_bit15_to_bit0: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd1) |=> (dout[31:1] == $past(din))
    );

    // When ctrl*sel is 2, dout[31:2] loads din.
    check_load_bit14_to_bit1: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd2) |=> (dout[31:2] == $past(din))
    );

    // When ctrl*sel is 3, dout[31:3] loads din.
    check_load_bit13_to_bit2: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd3) |=> (dout[31:3] == $past(din))
    );

    // When ctrl*sel is 4, dout[31:4] loads din.
    check_load_bit12_to_bit3: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd4) |=> (dout[31:4] == $past(din))
    );

    // When ctrl*sel is 5, dout[31:5] loads din.
    check_load_bit11_to_bit4: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd5) |=> (dout[31:5] == $past(din))
    );

    // When ctrl*sel is 6, dout[31:6] loads din.
    check_load_bit10_to_bit5: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd6) |=> (dout[31:6] == $past(din))
    );

    // When ctrl*sel is 7, dout[31:7] loads din.
    check_load_bit9_to_bit6: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd7) |=> (dout[31:7] == $past(din))
    );

    // When ctrl*sel is 8, dout[31:8] loads din.
    check_load_bit8_to_bit7: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd8) |=> (dout[31:8] == $past(din))
    );

    // When ctrl*sel is 9, dout[31:9] loads din.
    check_load_bit7_to_bit8: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd9) |=> (dout[31:9] == $past(din))
    );

    // When ctrl*sel is 10, dout[31:10] loads din.
    check_load_bit6_to_bit9: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd10) |=> (dout[31:10] == $past(din))
    );

    // When ctrl*sel is 11, dout[31:11] loads din.
    check_load_bit5_to_bit10: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd11) |=> (dout[31:11] == $past(din))
    );

    // When ctrl*sel is 12, dout[31:12] loads din.
    check_load_bit4_to_bit11: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd12) |=> (dout[31:12] == $past(din))
    );

    // When ctrl*sel is 13, dout[31:13] loads din.
    check_load_bit3_to_bit12: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd13) |=> (dout[31:13] == $past(din))
    );

    // When ctrl*sel is 14, dout[31:14] loads din.
    check_load_bit2_to_bit13: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd14) |=> (dout[31:14] == $past(din))
    );

    // When ctrl*sel is 15, dout[31:15] loads din.
    check_load_bit1_to_bit14: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd15) |=> (dout[31:15] == $past(din))
    );

    // When ctrl*sel is 16, dout[31:16] loads din.
    check_load_bit15_to_bit16: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd16) |=> (dout[31:16] == $past(din))
    );

    // When ctrl*sel is 17, dout[31:17] loads din.
    check_load_bit14_to_bit17: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd17) |=> (dout[31:17] == $past(din))
    );

    // When ctrl*sel is 18, dout[31:18] loads din.
    check_load_bit13_to_bit18: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd18) |=> (dout[31:18] == $past(din))
    );

    // When ctrl*sel is 19, dout[31:19] loads din.
    check_load_bit12_to_bit19: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd19) |=> (dout[31:19] == $past(din))
    );

    // When ctrl*sel is 20, dout[31:20] loads din.
    check_load_bit11_to_bit20: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd20) |=> (dout[31:20] == $past(din))
    );

    // When ctrl*sel is 21, dout[31:21] loads din.
    check_load_bit10_to_bit21: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd21) |=> (dout[31:21] == $past(din))
    );

    // When ctrl*sel is 22, dout[31:22] loads din.
    check_load_bit9_to_bit22: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd22) |=> (dout[31:22] == $past(din))
    );

    // When ctrl*sel is 23, dout[31:23] loads din.
    check_load_bit8_to_bit23: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd23) |=> (dout[31:23] == $past(din))
    );

    // When ctrl*sel is 24, dout[31:24] loads din.
    check_load_bit7_to_bit24: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd24) |=> (dout[31:24] == $past(din))
    );

    // When ctrl*sel is 25, dout[31:25] loads din.
    check_load_bit6_to_bit25: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd25) |=> (dout[31:25] == $past(din))
    );

    // When ctrl*sel is 26, dout[31:26] loads din.
    check_load_bit5_to_bit26: assert property (
        @(posedge clk) ((ctrl * sel) == 5'd26) |=> (dout[31:26] == $past(din))
    );

    // When ctrl*sel is 27