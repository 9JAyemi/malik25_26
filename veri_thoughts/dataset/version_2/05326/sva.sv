module wbdblpriarb_sva #(
    parameter DW = 32,
    parameter AW = 32
) (
    input  logic             i_clk,
    input  logic             i_rst,
    input  logic             i_a_cyc_a,
    input  logic             i_a_cyc_b,
    input  logic             i_a_stb_a,
    input  logic             i_a_stb_b,
    input  logic             i_a_we,
    input  logic [AW-1:0]    i_a_adr,
    input  logic [DW-1:0]    i_a_dat,
    input  logic [DW/8-1:0]  i_a_sel,
    input  logic             o_a_ack,
    input  logic             o_a_stall,
    input  logic             o_a_err,
    input  logic             i_b_cyc_a,
    input  logic             i_b_cyc_b,
    input  logic             i_b_stb_a,
    input  logic             i_b_stb_b,
    input  logic             i_b_we,
    input  logic [AW-1:0]    i_b_adr,
    input  logic [DW-1:0]    i_b_dat,
    input  logic [DW/8-1:0]  i_b_sel,
    input  logic             o_b_ack,
    input  logic             o_b_stall,
    input  logic             o_b_err,
    input  logic             o_cyc_a,
    input  logic             o_cyc_b,
    input  logic             o_stb_a,
    input  logic             o_stb_b,
    input  logic             o_we,
    input  logic [AW-1:0]    o_adr,
    input  logic [DW-1:0]    o_dat,
    input  logic [DW/8-1:0]  o_sel,
    input  logic             i_ack,
    input  logic             i_stall,
    input  logic             i_err,
    input  logic             r_a_owner
);

    // Reset returns ownership to A.
    check_reset_sets_a_owner: assert property (
        @(posedge i_clk) i_rst |=> (r_a_owner == 1'b1)
    );

    // If B is idle, A owns on the next clock.
    check_b_idle_returns_a_owner: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((!i_b_cyc_a) && (!i_b_cyc_b)) |=> (r_a_owner == 1'b1)
    );

    // B takes ownership only when A is idle and B is actively requesting.
    check_b_request_takes_owner_when_a_idle: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((i_b_cyc_a || i_b_cyc_b) && (!i_a_cyc_a) && (!i_a_cyc_b) && (i_b_stb_a || i_b_stb_b))
        |=> (r_a_owner == 1'b0)
    );

    // Otherwise the owner register holds its value.
    check_owner_holds_without_reassign_condition: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((i_b_cyc_a || i_b_cyc_b) && ((i_a_cyc_a || i_a_cyc_b) || !(i_b_stb_a || i_b_stb_b)))
        |=> $stable(r_a_owner)
    );

    // A ownership routes A cycle and write-enable.
    check_a_owner_routes_cycles_and_we: assert property (
        @(posedge i_clk) disable iff (i_rst)
        r_a_owner |-> ((o_cyc_a == i_a_cyc_a) && (o_cyc_b == i_a_cyc_b) && (o_we == i_a_we))
    );

    // B ownership routes B cycle and write-enable.
    check_b_owner_routes_cycles_and_we: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!r_a_owner) |-> ((o_cyc_a == i_b_cyc_a) && (o_cyc_b == i_b_cyc_b) && (o_we == i_b_we))
    );

    // When A owns, B sees no ack/err and a permanent stall.
    check_a_owner_blocks_b_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        r_a_owner |-> ((o_b_ack == 1'b0) && (o_b_err == 1'b0) && (o_b_stall == 1'b1))
    );

    // When B owns, A sees no ack/err and a permanent stall.
    check_b_owner_blocks_a_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!r_a_owner) |-> ((o_a_ack == 1'b0) && (o_a_err == 1'b0) && (o_a_stall == 1'b1))
    );

`ifdef ZERO_ON_IDLE
    // A ownership gates A strobes with A cycle activity.
    check_a_owner_routes_gated_strobes: assert property (
        @(posedge i_clk) disable iff (i_rst)
        r_a_owner |-> ((o_stb_a == (i_a_stb_a && i_a_cyc_a)) && (o_stb_b == (i_a_stb_b && i_a_cyc_b)))
    );

    // B ownership gates B strobes with B cycle activity.
    check_b_owner_routes_gated_strobes: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!r_a_owner) |-> ((o_stb_a == (i_b_stb_a && i_b_cyc_a)) && (o_stb_b == (i_b_stb_b && i_b_cyc_b)))
    );

    // Any active A-side output strobe routes A payload.
    check_a_owner_routes_payload_on_strobe: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (r_a_owner && (o_stb_a || o_stb_b))
        |-> ((o_adr == i_a_adr) && (o_dat == i_a_dat) && (o_sel == i_a_sel))
    );

    // Any active B-side output strobe routes B payload.
    check_b_owner_routes_payload_on_strobe: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((!r_a_owner) && (o_stb_a || o_stb_b))
        |-> ((o_adr == i_b_adr) && (o_dat == i_b_dat) && (o_sel == i_b_sel))
    );

    // No output strobe forces zero payload.
    check_zero_on_idle_zeroes_payload: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!(o_stb_a || o_stb_b)) |-> ((o_adr == '0) && (o_dat == '0) && (o_sel == '0))
    );

    // With A ownership and an active cycle, A sees the slave return signals.
    check_a_owner_active_cycle_routes_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (r_a_owner && (i_a_cyc_a || i_a_cyc_b))
        |-> ((o_a_ack == i_ack) && (o_a_stall == i_stall) && (o_a_err == i_err))
    );

    // With A ownership but no active cycle, A sees idle defaults.
    check_a_owner_idle_cycle_defaults_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (r_a_owner && !(i_a_cyc_a || i_a_cyc_b))
        |-> ((o_a_ack == 1'b0) && (o_a_stall == 1'b1) && (o_a_err == 1'b0))
    );

    // With B ownership and an active cycle, B sees the slave return signals.
    check_b_owner_active_cycle_routes_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((!r_a_owner) && (i_b_cyc_a || i_b_cyc_b))
        |-> ((o_b_ack == i_ack) && (o_b_stall == i_stall) && (o_b_err == i_err))
    );

    // With B ownership but no active cycle, B sees idle defaults.
    check_b_owner_idle_cycle_defaults_return_channel: assert property (
        @(posedge i_clk) disable iff (i_rst)
        ((!r_a_owner) && !(i_b_cyc_a || i_b_cyc_b))
        |-> ((o_b_ack == 1'b0) && (o_b_stall == 1'b1) && (o_b_err == 1'b0))
    );
`else
    // A ownership routes A strobes and payload directly.
    check_a_owner_routes_strobes_and_payload_direct: assert property (
        @(posedge i_clk) disable iff (i_rst)
        r_a_owner |-> ((o_stb_a == i_a_stb_a) && (o_stb_b == i_a_stb_b)
                    && (o_adr == i_a_adr) && (o_dat == i_a_dat) && (o_sel == i_a_sel))
    );

    // B ownership routes B strobes and payload directly.
    check_b_owner_routes_strobes_and_payload_direct: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!r_a_owner) |-> ((o_stb_a == i_b_stb_a) && (o_stb_b == i_b_stb_b)
                       && (o_adr == i_b_adr) && (o_dat == i_b_dat) && (o_sel == i_b_sel))
    );

    // A ownership routes the slave return channel directly to A.
    check_a_owner_routes_return_channel_direct: assert property (
        @(posedge i_clk) disable iff (i_rst)
        r_a_owner |-> ((o_a_ack == i_ack) && (o_a_stall == i_stall) && (o_a_err == i_err))
    );

    // B ownership routes the slave return channel directly to B.
    check_b_owner_routes_return_channel_direct: assert property (
        @(posedge i_clk) disable iff (i_rst)
        (!r_a_owner) |-> ((o_b_ack == i_ack) && (o_b_stall == i_stall) && (o_b_err == i_err))
    );
`endif

endmodule