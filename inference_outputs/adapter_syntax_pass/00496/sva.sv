module nonblocking_gate_sva (
    input logic clk,
    input logic [4:0] ctrl,
    input logic [1:0] din,
    input logic [0:0] sel,
    input logic [31:0] dout
);

    // dout increments by one on each clock.
    check_dout_increments: assert property (
        @(posedge clk) 1'b1 |=> (dout == ($past(dout) + 32'd1))
    );

    // When ctrl and sel select 0, dout[31:0] loads din.
    check_load_full_when_selected_0: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd0) |=> (dout[31:0] == $past(din))
    );

    // When ctrl and sel select 1, dout[31:1] loads din.
    check_load_bits_31_to_1_when_selected_1: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd1) |=> (dout[31:1] == $past(din))
    );

    // When ctrl and sel select 2, dout[31:2] loads din.
    check_load_bits_31_to_2_when_selected_2: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd2) |=> (dout[31:2] == $past(din))
    );

    // When ctrl and sel select 3, dout[31:3] loads din.
    check_load_bits_31_to_3_when_selected_3: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd3) |=> (dout[31:3] == $past(din))
    );

    // When ctrl and sel select 4, dout[31:4] loads din.
    check_load_bits_31_to_4_when_selected_4: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd4) |=> (dout[31:4] == $past(din))
    );

    // When ctrl and sel select 5, dout[31:5] loads din.
    check_load_bits_31_to_5_when_selected_5: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd5) |=> (dout[31:5] == $past(din))
    );

    // When ctrl and sel select 6, dout[31:6] loads din.
    check_load_bits_31_to_6_when_selected_6: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd6) |=> (dout[31:6] == $past(din))
    );

    // When ctrl and sel select 7, dout[31:7] loads din.
    check_load_bits_31_to_7_when_selected_7: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd7) |=> (dout[31:7] == $past(din))
    );

    // When ctrl and sel select 8, dout[31:8] loads din.
    check_load_bits_31_to_8_when_selected_8: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd8) |=> (dout[31:8] == $past(din))
    );

    // When ctrl and sel select 9, dout[31:9] loads din.
    check_load_bits_31_to_9_when_selected_9: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd9) |=> (dout[31:9] == $past(din))
    );

    // When ctrl and sel select 10, dout[31:10] loads din.
    check_load_bits_31_to_10_when_selected_10: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd10) |=> (dout[31:10] == $past(din))
    );

    // When ctrl and sel select 11, dout[31:11] loads din.
    check_load_bits_31_to_11_when_selected_11: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd11) |=> (dout[31:11] == $past(din))
    );

    // When ctrl and sel select 12, dout[31:12] loads din.
    check_load_bits_31_to_12_when_selected_12: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd12) |=> (dout[31:12] == $past(din))
    );

    // When ctrl and sel select 13, dout[31:13] loads din.
    check_load_bits_31_to_13_when_selected_13: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd13) |=> (dout[31:13] == $past(din))
    );

    // When ctrl and sel select 14, dout[31:14] loads din.
    check_load_bits_31_to_14_when_selected_14: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd14) |=> (dout[31:14] == $past(din))
    );

    // When ctrl and sel select 15, dout[31:15] loads din.
    check_load_bits_31_to_15_when_selected_15: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd15) |=> (dout[31:15] == $past(din))
    );

    // When ctrl and sel select 16, dout[31:16] loads din.
    check_load_bits_31_to_16_when_selected_16: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd16) |=> (dout[31:16] == $past(din))
    );

    // When ctrl and sel select 17, dout[31:17] loads din.
    check_load_bits_31_to_17_when_selected_17: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd17) |=> (dout[31:17] == $past(din))
    );

    // When ctrl and sel select 18, dout[31:18] loads din.
    check_load_bits_31_to_18_when_selected_18: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd18) |=> (dout[31:18] == $past(din))
    );

    // When ctrl and sel select 19, dout[31:19] loads din.
    check_load_bits_31_to_19_when_selected_19: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd19) |=> (dout[31:19] == $past(din))
    );

    // When ctrl and sel select 20, dout[31:20] loads din.
    check_load_bits_31_to_20_when_selected_20: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd20) |=> (dout[31:20] == $past(din))
    );

    // When ctrl and sel select 21, dout[31:21] loads din.
    check_load_bits_31_to_21_when_selected_21: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd21) |=> (dout[31:21] == $past(din))
    );

    // When ctrl and sel select 22, dout[31:22] loads din.
    check_load_bits_31_to_22_when_selected_22: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd22) |=> (dout[31:22] == $past(din))
    );

    // When ctrl and sel select 23, dout[31:23] loads din.
    check_load_bits_31_to_23_when_selected_23: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd23) |=> (dout[31:23] == $past(din))
    );

    // When ctrl and sel select 24, dout[31:24] loads din.
    check_load_bits_31_to_24_when_selected_24: assert property (
        @(posedge clk) (({ctrl, sel}) == 5'd24) |=> (d