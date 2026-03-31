module test_in_sva (
    input logic        clk,
    input logic        rst,
    input logic        enable,
    input logic [1:0]  ready,
    input logic [23:0] size,
    input logic [1:0]  activate,
    input logic [31:0] data,
    input logic        strobe,
    input logic [23:0] count
);

    // Reset clears all state and outputs.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // A ready value of 0 keeps the FSM idle.
    check_idle_when_ready_zero: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b00) && (activate == 2'b00)) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With no ready bit set, the FSM stays idle.
    check_idle_when_no_ready_bit: assert property (
        @(posedge clk) disable iff (rst)
        ((ready != 2'b00) && (activate == 2'b00)) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With enable low, the FSM stays idle.
    check_idle_when_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready != 2'b00) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] set, the FSM activates on the next cycle.
    check_activate_on_ready0: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b10) && (activate == 2'b00) && enable) |=> ((activate == 2'b01) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[1] set, the FSM activates on the next cycle.
    check_activate_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b01) && (activate == 2'b00) && enable) |=> ((activate == 2'b10) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable low, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1] clear, and enable high, the FSM stays idle.
    check_idle_on_ready01_enable_low: assert property (
        @(posedge clk) disable iff (rst)
        ((ready == 2'b11) && (activate == 2'b00) && !enable) |=> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // With ready[0] clear, ready[1]