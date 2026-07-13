module bus_fsm_sva (
    input logic gnt,
    input logic [1:0] state,
    input logic dly,
    input logic done,
    input logic req,
    input logic clk,
    input logic rst_n
);
    // State encodings (match RTL)
    localparam [1:0] IDLE  = 2'b00;
    localparam [1:0] BBUSY = 2'b01;
    localparam [1:0] BWAIT = 2'b10;
    localparam [1:0] BFREE = 2'b11;

    ///// Reset behavior /////
    // While reset is asserted, state is IDLE and gnt is 0.
    check_reset_idle_gnt0: assert property (
        @(posedge clk) !rst_n |-> (state == IDLE) && (gnt == 1'b0)
    );
    // On the first cycle after reset deasserts, state is IDLE and gnt is 0.
    check_first_cycle_after_reset_idle: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (state == IDLE) && (gnt == 1'b0)
    );

    ///// Next-state function /////
    // From IDLE: next = (req ? BBUSY : IDLE).
    check_state_trans_from_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) && ($past(state) == IDLE) |-> state == ($past(req) ? BBUSY : IDLE)
    );
    // From BBUSY: next = (!done ? BBUSY : (dly ? BWAIT : BFREE)).
    check_state_trans_from_bbusy: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) && ($past(state) == BBUSY) |-> state == ( !$past(done) ? BBUSY : ($past(dly) ? BWAIT : BFREE) )
    );
    // From BWAIT: next = (dly ? BWAIT : BFREE).
    check_state_trans_from_bwait: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) && ($past(state) == BWAIT) |-> state == ( $past(dly) ? BWAIT : BFREE )
    );
    // From BFREE: next = (req ? BBUSY : IDLE).
    check_state_trans_from_bfree: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) && ($past(state) == BFREE) |-> state == ($past(req) ? BBUSY : IDLE)
    );

    ///// gnt definition /////
    // gnt is asserted iff state is BBUSY or BWAIT (matches RTL combinational definition).
    check_gnt_definition: assert property (
        @(posedge clk) disable iff (!rst_n) gnt == ((state == BBUSY) | (state == BWAIT))
    );
    // In IDLE, gnt must be 0.
    check_gnt_low_in_idle: assert property (
        @(posedge clk) disable iff (!rst_n) (state == IDLE) |-> (gnt == 1'b0)
    );
    // In BFREE, gnt must be 0.
    check_gnt_low_in_bfree: assert property (
        @(posedge clk) disable iff (!rst_n) (state == BFREE) |-> (gnt == 1'b0)
    );
    // A rising gnt implies we entered BBUSY or BWAIT this cycle.
    check_gnt_rise_targets_busy_or_wait: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(gnt) |-> ((state == BBUSY) || (state == BWAIT))
    );
    // A falling gnt implies we entered IDLE or BFREE this cycle.
    check_gnt_fall_targets_idle_or_free: assert property (
        @(posedge clk) disable iff (!rst_n) $fell(gnt) |-> ((state == IDLE) || (state == BFREE))
    );
endmodule