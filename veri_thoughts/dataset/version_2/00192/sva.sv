module oh_iddr_sva #(parameter int DW = 1) (
    input logic          clk,
    input logic          ce,
    input logic [DW-1:0] din,
    input logic [DW-1:0] q1,
    input logic [DW-1:0] q2,
    input logic [DW-1:0] q1_sl,
    input logic [DW-1:0] q2_sh
);

    // q1_sl captures din on an enabled rising edge.
    check_q1sl_captures_din: assert property (
        @(posedge clk) disable iff (1'b0)
        ce |=> (q1_sl == $past(din))
    );

    // q1_sl holds its value when ce is low.
    check_q1sl_holds_when_ce_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !ce |=> (q1_sl == $past(q1_sl))
    );

    // q1 reflects the previously sampled q1_sl value.
    check_q1_updates_from_q1sl: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (q1 == $past(q1_sl))
    );

    // q2 reflects the previously sampled q2_sh value.
    check_q2_updates_from_q2sh: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (q2 == $past(q2_sh))
    );

    // An enabled din sample reaches q1 two rising-edge samples later.
    check_q1_enabled_path_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        ce |=> ##1 (q1 == $past(din, 2))
    );

endmodule