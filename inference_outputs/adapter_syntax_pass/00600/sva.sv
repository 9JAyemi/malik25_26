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
    check_reset_state: assert property (
        @(posedge clk)
        rst |-> ((activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0) && (count == 24'd0))
    );

    // A valid ready and enabled cycle starts count and sets activate[0].
    check_start_cycle: assert property (
        @(posedge clk) disable iff (rst)
        ((ready > 2'd0) && (activate == 2'b00) && enable) |=> ((count == 24'd0) && (activate == 2'b01))
    );

    // A valid ready and enabled cycle with ready[0] low sets activate[1].
    check_start_cycle_ready1: assert property (
        @(posedge clk) disable iff (rst)
        ((ready > 2'd0) && (activate == 2'b00) && enable && !ready[0]) |=> ((count == 24'd0) && (activate == 2'b10))
    );

    // With no valid start and activate[1], the state holds.
    check_hold_when_no_start_and_no_activate1: assert property (
        @(posedge clk) disable iff (rst)
        (((ready <= 2'd0) || (activate != 2'b00)) && (activate != 2'b10)) |=> $stable({activate, count, data, strobe})
    );

    // With no valid start and activate[0], activate[1] is cleared.
    check_clear_activate1_when_no_start: assert property (
        @(posedge clk) disable iff (rst)
        (((ready <= 2'd0) || (activate != 2'b00)) && (activate == 2'b01)) |=> (activate == 2'b00)
    );

    // With activate[1] and count below size, strobe is asserted and count increments.
    check_increment_when_active_and_below_size: assert property (
        @(posedge clk) disable iff (rst)
        ((activate == 2'b10) && (count < size)) |=> ((strobe == 1'b1) && (count == ($past(count) + 24'd1)) && (data == {24'd0, $past(count)}))
    );

    // With activate[1] and count at or above size, activate[1] is cleared.
    check_clear_activate1_when_done: assert property (
        @(posedge clk) disable iff (rst)
        ((activate == 2'b10) && (count >= size)) |=> (activate == 2'b00)
    );

    // With activate[0] and no valid start, activate[0] is cleared.
    check_clear_activate0_when_no_start: assert property (
        @(posedge clk) disable iff (rst)
        (((ready <= 2'd0) || (activate != 2'b00)) && (activate == 2'b01)) |=> (activate == 2'b00)
    );

    // strobe can only be high when activate[1] is set.
    check_strobe_implies_activate1: assert property (
        @(posedge clk) disable iff (rst)
        strobe |-> (activate == 2'b10)
    );

    // strobe is never asserted when activate is zero.
    check_strobe_never_when_no_activate: assert property (
        @(posedge clk) disable iff (rst)
        (activate == 2'b00) |-> (strobe == 1'b0)
    );

endmodule