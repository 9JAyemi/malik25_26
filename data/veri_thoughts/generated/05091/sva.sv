module reg_ena_rst_sva (
    input logic clk,
    input logic ena,
    input logic d,
    input logic rst,
    input logic q
);

    // Reset clears q.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 1'b0)
    );

    // Enable loads a 1 from d.
    check_enable_loads_one: assert property (
        @(posedge clk) disable iff (rst)
        (ena && (d == 1'b1)) |=> (q == 1'b1)
    );

    // Enable loads a 0 from d.
    check_enable_loads_zero: assert property (
        @(posedge clk) disable iff (rst)
        (ena && (d == 1'b0)) |=> (q == 1'b0)
    );

    // q holds high when disabled.
    check_hold_one_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        ((!ena) && (q == 1'b1)) |=> (q == 1'b1)
    );

    // q holds low when disabled.
    check_hold_zero_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        ((!ena) && (q == 1'b0)) |=> (q == 1'b0)
    );

endmodule