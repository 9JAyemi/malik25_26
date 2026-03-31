module flip_flop_sva (
    input logic clk,
    input logic rst,
    input logic data,
    input logic q,
    input logic q_bar,
    input logic [1:0] type // type parameter as input for SVA
);
    // Clock: clk (posedge). Reset: rst (synchronous, active-high). Mixed logic: sequential with combinational outputs.

    ///// Reset behavior /////
    // When rst is HIGH, outputs drive 1/0 for D/SR and 0/1 for JK/T.
    reset_outputs: assert property (
        @(posedge clk) rst |-> (q == (type[0] ? 1'b1 : 1'b0)) && (q_bar == (type[0] ? 1'b0 : 1'b1))
    );

    ///// D-type behavior (type 0) /////
    // For D-type, next q equals data (reset already handled).
    d_type_q_next: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd0) |-> ##1 (q == $past(data))
    );
    // For D-type, next q_bar equals ~data (reset already handled).
    d_type_qbar_next: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd0) |-> ##1 (q_bar == ~$past(data))
    );

    ///// JK-type behavior (type 1) /////
    // For JK-type with data=1, q toggles to ~q_bar and q_bar toggles to ~q (reset already handled).
    jk_set_toggle: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd1 && data) |-> ##1 (q == ~$past(q_bar) && q_bar == ~$past(q))
    );
    // For JK-type with data=0, q and q_bar hold (reset already handled).
    jk_hold: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd1 && !data) |-> ##1 (q == $past(q) && q_bar == $past(q_bar))
    );

    ///// T-type behavior (type 2) /////
    // For T-type with data=1, q toggles and q_bar toggles (reset already handled).
    t_toggle: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd2 && data) |-> ##1 (q == ~$past(q) && q_bar == ~$past(q_bar))
    );
    // For T-type with data=0, q and q_bar hold (reset already handled).
    t_hold: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd2 && !data) |-> ##1 (q == $past(q) && q_bar == $past(q_bar))
    );

    ///// SR-type behavior (type 3) /////
    // For SR-type with data=1, q loads 0 and q_bar loads 1 (reset already handled).
    sr_set: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd3 && data) |-> ##1 (q == 1'b0 && q_bar == 1'b1)
    );
    // For SR-type with data=0, q and q_bar hold (reset already handled).
    sr_hold: assert property (
        @(posedge clk) disable iff (rst) (type == 2'd3 && !data) |-> ##1 (q == $past(q) && q_bar == $past(q_bar))
    );

    ///// Combinational consistency /////
    // q_bar is always the bitwise complement of q (reset already handled).
    qbar_complement: assert property (
        @(posedge clk) disable iff (rst) (q_bar == ~q)
    );

    ///// Hold behavior /////
    // For all types, when data=0, q and q_bar hold their values (reset already handled).
    hold_when_data0: assert property (
        @(posedge clk) disable iff (rst) (!data) |-> ##1 (q == $past(q) && q_bar == $past(q_bar))
    );

endmodule