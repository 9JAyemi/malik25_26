module top_module_sva (
    input logic       clk,
    input logic       areset,
    input logic       load,
    input logic       ena,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] q1,
    input logic [3:0] q2,
    input logic [3:0] out
);

    // Clock: clk
    // Reset: areset, async active-high
    // Mixed logic: q1/q2 are sequential, out is combinational

    // Reset forces all state-derived outputs to zero.
    check_reset_clears_state: assert property (
        @(posedge clk)
        areset |-> (q1 == 4'b0000 && q2 == 4'b0000 && out == 4'b0000)
    );

    // Load captures data1/data2 into q1/q2 on the next cycle, regardless of ena.
    check_load_captures_q: assert property (
        @(posedge clk) disable iff (areset)
        load |=> (q1 == $past(data1) && q2 == $past(data2))
    );

    // Load updates out to the XOR of the loaded internal values.
    check_load_updates_out: assert property (
        @(posedge clk) disable iff (areset)
        load |=> (out == ($past(data1) ^ $past(data2)))
    );

    // With ena and no load, q1 and q2 shift left and insert 0 in the LSB.
    check_shift_updates_q: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (q1 == {$past(q1[2:0]), 1'b0} &&
                            q2 == {$past(q2[2:0]), 1'b0})
    );

    // With ena and no load, out shifts left and inserts 0 in the LSB.
    check_shift_updates_out: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (out == {$past(out[2:0]), 1'b0})
    );

    // With neither load nor ena, q1, q2, and out hold their values.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (q1 == $past(q1) &&
                             q2 == $past(q2) &&
                             out == $past(out))
    );

endmodule