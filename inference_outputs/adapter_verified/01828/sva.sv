module counter_mod_sva(
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic [3:0] q,
    input logic carry
);

// Reset drives q and carry low on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (q == 4'b0000) && (carry == 1'b0)
    );

// Up counter increments q when not at max.
    check_up_increment: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0) && (q != 4'b1111) |=> (q == ($past(q) + 4'b0001)) && (carry == 1'b0)
    );

// Up counter wraps to zero when at max.
    check_up_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0) && (q == 4'b1111) |=> (q == 4'b0000) && (carry == 1'b1)
    );

// Down counter decrements q when not at zero.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1) && (q != 4'b0000) |=> (q == ($past(q) - 4'b0001)) && (carry == 1'b0)
    );

// Down counter wraps to max when at zero.
    check_down_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1) && (q == 4'b0000) |=> (q == 4'b1111) && (carry == 1'b1)
    );

// Carry is high exactly when a counter wraps.
    check_carry_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        ((up_down == 1'b0) && (q == 4'b1111)) || ((up_down == 1'b1) && (q == 4'b0000)) |-> (carry == 1'b1)
    );

// Carry is low exactly when a counter does not wrap.
    check_carry_on_no_wrap: assert property (
        @(posedge clk) disable iff (rst)
        !(((up_down == 1'b0) && (q == 4'b1111)) || ((up_down == 1'b1) && (q == 4'b0000))) |-> (carry == 1'b0)
    );

endmodule
