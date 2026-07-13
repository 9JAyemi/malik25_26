module crossbar36_sva (
    input logic clk,
    input logic reset,
    input logic clear,
    input logic cross,
    input logic [35:0] data0_i,
    input logic src0_rdy_i,
    input logic dst0_rdy_o,
    input logic [35:0] data1_i,
    input logic src1_rdy_i,
    input logic dst1_rdy_o,
    input logic [35:0] data0_o,
    input logic src0_rdy_o,
    input logic dst0_rdy_i,
    input logic [35:0] data1_o,
    input logic src1_rdy_o,
    input logic dst1_rdy_i,
    // Internal signals from RTL
    input logic cross_int,
    input logic active0,
    input logic active1,
    input logic active0_next,
    input logic active1_next
);

    ///// Reset behavior /////
    // Reset/clear drives active0 LOW.
    reset_active0_low: assert property (
        @(posedge clk) (reset | clear) |-> (active0 == 1'b0)
    );
    // Reset/clear drives active1 LOW.
    reset_active1_low: assert property (
        @(posedge clk) (reset | clear) |-> (active1 == 1'b0)
    );
    // Reset/clear drives cross_int LOW.
    reset_cross_int_low: assert property (
        @(posedge clk) (reset | clear) |-> (cross_int == 1'b0)
    );

    ///// Crossbar muxing /////
    // When not crossed, all channels are pass-through.
    mux_passthrough_when_no_cross: assert property (
        @(posedge clk) disable iff (reset | clear)
            (cross_int == 1'b0)
            |-> (data0_o == data0_i)
             && (data1_o == data1_i)
             && (src0_rdy_o == src0_rdy_i)
             && (src1_rdy_o == src1_rdy_i)
             && (dst0_rdy_o == dst0_rdy_i)
             && (dst1_rdy_o == dst1_rdy_i)
    );
    // When crossed, channels are swapped.
    mux_swap_when_cross: assert property (
        @(posedge clk) disable iff (reset | clear)
            (cross_int == 1'b1)
            |-> (data0_o == data1_i)
             && (data1_o == data0_i)
             && (src0_rdy_o == src1_rdy_i)
             && (src1_rdy_o == src0_rdy_i)
             && (dst0_rdy_o == dst1_rdy_i)
             && (dst1_rdy_o == dst0_rdy_i)
    );

    ///// Channel activity tracking /////
    // On handshake, active0 loads inverted data0_i[33] on next cycle.
    active0_updates_on_handshake: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && $past(src0_rdy_i & dst0_rdy_o))
            |-> (active0 == ~ $past(data0_i[33]))
    );
    // Without handshake, active0 holds its previous value.
    active0_holds_without_handshake: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && !$past(src0_rdy_i & dst0_rdy_o))
            |-> (active0 == $past(active0))
    );
    // On handshake, active1 loads inverted data1_i[33] on next cycle.
    active1_updates_on_handshake: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && $past(src1_rdy_i & dst1_rdy_o))
            |-> (active1 == ~ $past(data1_i[33]))
    );
    // Without handshake, active1 holds its previous value.
    active1_holds_without_handshake: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && !$past(src1_rdy_i & dst1_rdy_o))
            |-> (active1 == $past(active1))
    );

    ///// Cross selection update rules /////
    // cross_int may change only when both active*_next were 0 in the previous cycle.
    cross_int_changes_only_when_idle: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && $changed(cross_int))
            |-> $past((~active0_next) & (~active1_next))
    );
    // If either channel was active in the previous cycle, cross_int holds.
    cross_int_holds_when_busy: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && !$past((~active0_next) & (~active1_next)))
            |-> (cross_int == $past(cross_int))
    );
    // When both were idle in the previous cycle, cross_int loads cross.
    cross_int_updates_from_cross_when_idle: assert property (
        @(posedge clk) disable iff (reset | clear)
            ($past(! (reset | clear)) && $past((~active0_next) & (~active1_next)))
            |-> (cross_int == $past(cross))
    );

endmodule