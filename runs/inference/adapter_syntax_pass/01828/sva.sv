module counter_mod_rtl_sva (
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic [3:0] q,
    input logic carry
);

    // Reset forces the counter to zero and clears carry.
    check_reset_state: assert property (
        @(posedge clk) rst |-> (q == 4'h0) && (carry == 1'b0)
    );

    // Up count wraps from 15 to 0 and raises carry.
    check_up_wrap_carry: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0) && (q == 4'hF) |=> (q == 4'h0) && (carry == 1'b1)
    );

    // Up count increments by one below 15 and clears carry.
    check_up_increment: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b0) && (q != 4'hF) |=> (q == ($past(q) + 4'h1)) && (carry == 1'b0)
    );

    // Down count wraps from 0 to 15 and raises carry.
    check_down_wrap_carry: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1) && (q == 4'h0) |=> (q == 4'hF) && (carry == 1'b1)
    );

    // Down count decrements by one above 0 and clears carry.
    check_down_decrement: assert property (
        @(posedge clk) disable iff (rst)
        (up_down == 1'b1) && (q != 4'h0) |=> (q == ($past(q) - 4'h1)) && (carry == 1'b0)
    );

    // Carry is high only when the previous cycle was a wrap.
    check_carry_only_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        carry |-> (($past(up_down) == 1'b0) && ($past(q) == 4'hF)) ||
                 (($past(up_down) == 1'b1) && ($past(q) == 4'h0))
    );

endmodule