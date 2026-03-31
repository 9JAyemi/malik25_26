module counter_mod_rtl_sva (
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic [3:0] q,
    input logic carry
);

    // Reset forces the counter and carry low.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> (q == 4'b0000) && (carry == 1'b0)
    );

    // In up mode, a terminal count wraps and raises carry.
    check_up_wrap_and_carry: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0 && q == 4'b1111) |=> (q == 4'b0000) && (carry == 1'b1)
    );

    // In up mode, a non-terminal count increments and clears carry.
    check_up_increment: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0 && q != 4'b1111) |=> (q == ($past(q) + 4'b0001)) && (carry == 1'b0)
    );

    // In down mode, a terminal count wraps and raises carry.
    check_down_wrap_and_carry: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1 && q == 4'b0000) |=> (q == 4'b1111) && (carry == 1'b1)
    );

    // In down mode, a non-terminal count decrements and clears carry.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1 && q != 4'b0000) |=> (q == ($past(q) - 4'b0001)) && (carry == 1'b0)
    );

    // Carry is high only after a wrap in either counting direction.
    check_carry_only_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        carry |-> ($past(q) == (up_down ? 4'b0000 : 4'b1111))
    );

endmodule