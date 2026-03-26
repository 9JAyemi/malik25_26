module top_module_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    input logic [7:0] q,
    input logic [7:0] sum
);

    // sum reflects the combinational addition of d1 and d2.
    check_sum_matches_addition: assert property (
        @(posedge clk) disable iff (rst)
            sum == (d1 + d2)
    );

    // sum does not depend on sel.
    check_sum_independent_of_sel: assert property (
        @(posedge clk) disable iff (rst)
            $changed(sel) && $stable(d1) && $stable(d2) |-> $stable(sum)
    );

    // With sel low, q captures d1 on the next clock.
    check_q_captures_d1_when_sel_low: assert property (
        @(posedge clk) disable iff (rst)
            !sel |=> (q == $past(d1))
    );

    // With sel high, q captures d2 on the next clock.
    check_q_captures_d2_when_sel_high: assert property (
        @(posedge clk) disable iff (rst)
            sel |=> (q == $past(d2))
    );

    // If reset stays asserted across clocks, q remains zero.
    check_q_zero_while_reset_held: assert property (
        @(posedge clk)
            rst && $past(rst) |-> (q == 8'h00)
    );

    // On the first clock after reset deasserts, q is still zero.
    check_q_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (rst)
            $fell(rst) |-> (q == 8'h00)
    );

endmodule