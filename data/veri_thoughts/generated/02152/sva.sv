module dynamic_gate_sva (
    input logic in,
    input logic clk,
    input logic out
);
    // out equals in from the previous clock cycle.
    check_out_equals_prev_in: assert property (
        @(posedge clk) disable iff ($initstate) out == $past(in)
    );

    // If in is 1 at a clock edge, out becomes 1 at the next clock edge.
    check_in1_out1_next: assert property (
        @(posedge clk) disable iff ($initstate) in |-> ##1 out
    );

    // If in is 0 at a clock edge, out becomes 0 at the next clock edge.
    check_in0_out0_next: assert property (
        @(posedge clk) disable iff ($initstate) !in |-> ##1 !out
    );

    // A rising edge on out implies previous-cycle in was 1.
    check_out_rise_prev_in1: assert property (
        @(posedge clk) disable iff ($initstate) $rose(out) |-> $past(in)
    );

    // A falling edge on out implies previous-cycle in was 0.
    check_out_fall_prev_in0: assert property (
        @(posedge clk) disable iff ($initstate) $fell(out) |-> !$past(in)
    );

    // After initialization, out is never X/Z at each clock edge.
    check_out_known: assert property (
        @(posedge clk) disable iff ($initstate) !$isunknown(out)
    );
endmodule