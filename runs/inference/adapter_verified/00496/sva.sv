module nonblocking_gate_sva (
    input logic clk,
    input logic [4:0] ctrl,
    input logic [1:0] din,
    input logic [0:0] sel,
    input logic [31:0] dout
);

// dout increments by one every cycle.
    check_dout_increment: assert property (
        @(posedge clk) 1'b1 |=> (dout == ($past(dout) + 32'd1))
    );

// When ctrl is 0 and sel is 0, dout[31:0] loads din.
    check_load_ctrl0_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd0) && (sel == 1'b0)) |=> (dout[31:0] == $past(din))
    );

// When ctrl is 0 and sel is 1, dout[31:1] loads din.
    check_load_ctrl0_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd0) && (sel == 1'b1)) |=> (dout[31:1] == $past(din))
    );

// When ctrl is 1 and sel is 0, dout[31:2] loads din.
    check_load_ctrl1_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd1) && (sel == 1'b0)) |=> (dout[31:2] == $past(din))
    );

// When ctrl is 1 and sel is 1, dout[31:3] loads din.
    check_load_ctrl1_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd1) && (sel == 1'b1)) |=> (dout[31:3] == $past(din))
    );

// When ctrl is 2 and sel is 0, dout[31:4] loads din.
    check_load_ctrl2_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd2) && (sel == 1'b0)) |=> (dout[31:4] == $past(din))
    );

// When ctrl is 2 and sel is 1, dout[31:5] loads din.
    check_load_ctrl2_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd2) && (sel == 1'b1)) |=> (dout[31:5] == $past(din))
    );

// When ctrl is 3 and sel is 0, dout[31:6] loads din.
    check_load_ctrl3_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd3) && (sel == 1'b0)) |=> (dout[31:6] == $past(din))
    );

// When ctrl is 3 and sel is 1, dout[31:7] loads din.
    check_load_ctrl3_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd3) && (sel == 1'b1)) |=> (dout[31:7] == $past(din))
    );

// When ctrl is 4 and sel is 0, dout[31:8] loads din.
    check_load_ctrl4_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd4) && (sel == 1'b0)) |=> (dout[31:8] == $past(din))
    );

// When ctrl is 4 and sel is 1, dout[31:9] loads din.
    check_load_ctrl4_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd4) && (sel == 1'b1)) |=> (dout[31:9] == $past(din))
    );

// When ctrl is 5 and sel is 0, dout[31:10] loads din.
    check_load_ctrl5_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd5) && (sel == 1'b0)) |=> (dout[31:10] == $past(din))
    );

// When ctrl is 5 and sel is 1, dout[31:11] loads din.
    check_load_ctrl5_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd5) && (sel == 1'b1)) |=> (dout[31:11] == $past(din))
    );

// When ctrl is 6 and sel is 0, dout[31:12] loads din.
    check_load_ctrl6_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd6) && (sel == 1'b0)) |=> (dout[31:12] == $past(din))
    );

// When ctrl is 6 and sel is 1, dout[31:13] loads din.
    check_load_ctrl6_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd6) && (sel == 1'b1)) |=> (dout[31:13] == $past(din))
    );

// When ctrl is 7 and sel is 0, dout[31:14] loads din.
    check_load_ctrl7_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd7) && (sel == 1'b0)) |=> (dout[31:14] == $past(din))
    );

// When ctrl is 7 and sel is 1, dout[31:15] loads din.
    check_load_ctrl7_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd7) && (sel == 1'b1)) |=> (dout[31:15] == $past(din))
    );

// When ctrl is 8 and sel is 0, dout[31:16] loads din.
    check_load_ctrl8_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd8) && (sel == 1'b0)) |=> (dout[31:16] == $past(din))
    );

// When ctrl is 8 and sel is 1, dout[31:17] loads din.
    check_load_ctrl8_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd8) && (sel == 1'b1)) |=> (dout[31:17] == $past(din))
    );

// When ctrl is 9 and sel is 0, dout[31:18] loads din.
    check_load_ctrl9_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd9) && (sel == 1'b0)) |=> (dout[31:18] == $past(din))
    );

// When ctrl is 9 and sel is 1, dout[31:19] loads din.
    check_load_ctrl9_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd9) && (sel == 1'b1)) |=> (dout[31:19] == $past(din))
    );

// When ctrl is 10 and sel is 0, dout[31:20] loads din.
    check_load_ctrl10_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd10) && (sel == 1'b0)) |=> (dout[31:20] == $past(din))
    );

// When ctrl is 10 and sel is 1, dout[31:21] loads din.
    check_load_ctrl10_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd10) && (sel == 1'b1)) |=> (dout[31:21] == $past(din))
    );

// When ctrl is 11 and sel is 0, dout[31:22] loads din.
    check_load_ctrl11_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd11) && (sel == 1'b0)) |=> (dout[31:22] == $past(din))
    );

// When ctrl is 11 and sel is 1, dout[31:23] loads din.
    check_load_ctrl11_sel1: assert property (
        @(posedge clk) ((ctrl == 5'd11) && (sel == 1'b1)) |=> (dout[31:23] == $past(din))
    );

// When ctrl is 12 and sel is 0, dout[31:24] loads din.
    check_load_ctrl12_sel0: assert property (
        @(posedge clk) ((ctrl == 5'd12) && (sel == 1'b0)) |=> (dout[31:24] == $past(din))
    );

// When ctrl is 12 and sel is 1, dout[31:25] loads din.
    check_load