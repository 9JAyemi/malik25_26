module min_shift_reg_sva (
    input logic        clk,
    input logic        areset,
    input logic        load,
    input logic        ena,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  c,
    input logic [7:0]  d,
    input logic [3:0]  q
);

    // Sampled reset forces the register output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk)
        areset |-> (q == 4'b0000)
    );

    // Load writes 00 when the first encoder comparison d<c is true.
    check_load_selects_00_d_lt_c: assert property (
        @(posedge clk) disable iff (areset)
        load && (d < c) |=> (q == 4'b0000)
    );

    // Load writes 01 when d<c is false and c<b is true.
    check_load_selects_01_c_lt_b: assert property (
        @(posedge clk) disable iff (areset)
        load && !(d < c) && (c < b) |=> (q == 4'b0001)
    );

    // Load writes 10 when earlier comparisons fail and b<a is true.
    check_load_selects_10_b_lt_a: assert property (
        @(posedge clk) disable iff (areset)
        load && !(d < c) && !(c < b) && (b < a) |=> (q == 4'b0010)
    );

    // Load writes 11 when all encoder comparisons fail.
    check_load_selects_11_default: assert property (
        @(posedge clk) disable iff (areset)
        load && !(d < c) && !(c < b) && !(b < a) |=> (q == 4'b0011)
    );

    // Enable shifts the register left and inserts 0 into bit 0.
    check_shift_on_enable: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (q == {$past(q[2:0]), 1'b0})
    );

    // With neither load nor enable, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (q == $past(q))
    );

endmodule