module shift_register_sva (
    input logic clk,
    input logic areset,  // active-low async reset in RTL
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    ///// Reset behavior /////
    // While reset is asserted (low), q must be zero.
    reset_forces_zero: assert property (
        @(posedge clk) (areset == 1'b0) |-> (q == 4'b0000)
    );

    ///// Load behavior /////
    // Loading captures data into q on the next cycle.
    load_updates_q: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && load) |=> (q == $past(data))
    );

    // Load has priority over enable when both are asserted.
    load_overrides_enable: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && load && ena) |=> (q == $past(data))
    );

    ///// Enable (shift) behavior /////
    // With enable and no load, q shifts left by 1 and inserts 0 at LSB.
    enable_shifts_left: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && ena && !load) |=> (q == { $past(q[2:0]), 1'b0 })
    );

    // With enable and no load, the LSB becomes 0 on the next cycle.
    enable_sets_lsb_zero: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (ena && !load) |=> (q[0] == 1'b0)
    );

    // With enable and no load, next MSB equals previous bit[2].
    enable_shifts_msb_from_bit2: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && ena && !load) |=> (q[3] == $past(q[2]))
    );

    ///// Hold behavior /////
    // With neither load nor enable, q holds its value.
    hold_when_idle: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && !load && !ena) |=> (q == $past(q))
    );

    ///// Corner cases /////
    // Shifting a zero value with enable and no load keeps q at zero.
    shift_zero_stays_zero: assert property (
        @(posedge clk) disable iff (areset == 1'b0) (!$initstate && ena && !load && ($past(q) == 4'b0000)) |=> (q == 4'b0000)
    );

endmodule