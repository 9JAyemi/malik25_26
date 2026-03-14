module shift_register_left_sva (
    input logic clk,
    input logic areset_n,  // async active-low reset
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);
    // Clock: posedge clk. Reset: areset_n active-low, asynchronous.
    // Logic: sequential with async reset; load has priority over shift; else hold.

    ///// Reset behavior /////
    // When reset is asserted at the clock edge, q is zero.
    check_reset_clears_q: assert property (
        @(posedge clk) (!areset_n) |-> (q == 4'b0000)
    );

    ///// Load behavior /////
    // On load, q updates with data on the next cycle.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (!areset_n) load |=> (q == $past(data))
    );

    // Load has priority over ena when both are asserted.
    check_priority_load_over_ena: assert property (
        @(posedge clk) disable iff (!areset_n) (load && ena) |=> (q == $past(data))
    );

    ///// Shift behavior /////
    // On ena without load, q shifts left by one with zero fill.
    check_shift_left_when_ena_only: assert property (
        @(posedge clk) disable iff (!areset_n) (ena && !load) |=> (q == {$past(q[2:0]), 1'b0})
    );

    // On shift, LSB becomes zero.
    check_shift_lsb_zero: assert property (
        @(posedge clk) disable iff (!areset_n) (ena && !load) |=> (q[0] == 1'b0)
    );

    // On shift, MSB takes previous bit2.
    check_shift_msb_from_bit2: assert property (
        @(posedge clk) disable iff (!areset_n) (ena && !load) |=> (q[3] == $past(q[2]))
    );

    // On shift, bit2 takes previous bit1.
    check_shift_bit2_from_bit1: assert property (
        @(posedge clk) disable iff (!areset_n) (ena && !load) |=> (q[2] == $past(q[1]))
    );

    // On shift, bit1 takes previous bit0.
    check_shift_bit1_from_bit0: assert property (
        @(posedge clk) disable iff (!areset_n) (ena && !load) |=> (q[1] == $past(q[0]))
    );

    ///// Hold behavior /////
    // When neither load nor ena is asserted, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!areset_n) (!load && !ena) |=> (q == $past(q))
    );
endmodule