module EtherCAT_master_sva #(
    parameter int n = 8, 
    parameter int m = 4
)(
    input  logic [n-1:0] in_send,
    input  logic [m-1:0] in_receive,
    input  logic         clk,
    input  logic         rst,
    input  logic [n-1:0] out_receive,
    input  logic [m-1:0] out_send
);

    ///// Reset behavior /////
    // After any cycle with rst HIGH, outputs are zero in the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (out_receive == '0) && (out_send == '0)
    );

    // While rst is held HIGH across consecutive cycles, outputs are zero.
    reset_held_forces_zero: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (out_receive == '0) && (out_send == '0)
    );

    // While rst is held HIGH across consecutive cycles, outputs do not change.
    reset_held_outputs_stable: assert property (
        @(posedge clk) ($past(rst) && rst) |-> $stable(out_receive) && $stable(out_send)
    );

    // On the first cycle after rst was HIGH (deassertion at this clock), outputs are still zero this cycle.
    deassertion_cycle_outputs_zero: assert property (
        @(posedge clk) ($past(rst) && !rst) |-> (out_receive == '0) && (out_send == '0)
    );

    // A rising edge of rst leads to zeroed outputs by the next cycle.
    rise_reset_zero_next: assert property (
        @(posedge clk) $rose(rst) |=> (out_receive == '0) && (out_send == '0)
    );

    ///// Coverage (non-constraining) /////
    // Observe pass-through of in_send to out_receive in one cycle when not in reset.
    cover_receive_pass: cover property (
        @(posedge clk) disable iff (rst) out_receive == $past(in_send)
    );

    // Observe pass-through of in_receive to out_send in one cycle when not in reset.
    cover_send_pass: cover property (
        @(posedge clk) disable iff (rst) out_send == $past(in_receive)
    );

endmodule