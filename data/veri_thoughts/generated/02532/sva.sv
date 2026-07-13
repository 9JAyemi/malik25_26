module shift_register_sva (
    input logic clk,
    input logic d,
    input logic [2:0] q
);

    // Next cycle q equals previous q[1:0] concatenated with current d.
    check_shift_next: assert property (
        @(posedge clk) 1'b1 |=> (q == { $past(q[1:0]), d })
    );

    // LSB loads current d each cycle.
    check_lsb_loads_d: assert property (
        @(posedge clk) 1'b1 |=> (q[0] == d)
    );

    // q[1] becomes previous q[0].
    check_middle_shifts_from_lsb: assert property (
        @(posedge clk) 1'b1 |=> (q[1] == $past(q[0]))
    );

    // q[2] becomes previous q[1].
    check_msb_shifts_from_mid: assert property (
        @(posedge clk) 1'b1 |=> (q[2] == $past(q[1]))
    );

    // Upper pair shifts from lower pair.
    check_upper_pair_shift: assert property (
        @(posedge clk) 1'b1 |=> (q[2:1] == $past(q[1:0]))
    );

    // q[1] equals d delayed by 1 cycle.
    check_q1_delays_d_by1: assert property (
        @(posedge clk) 1'b1 |=> (q[1] == $past(d))
    );

    // q[2] equals d delayed by 2 cycles.
    check_q2_delays_d_by2: assert property (
        @(posedge clk) 1'b1 |=> (q[2] == $past(d,2))
    );

endmodule