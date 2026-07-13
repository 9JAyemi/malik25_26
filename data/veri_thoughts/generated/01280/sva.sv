module t_order_a_sva (
    input logic clk,
    input logic [7:0] a_to_clk_levm3,
    input logic [7:0] b_to_clk_levm1,
    input logic [7:0] c_com_levs10,
    input logic [7:0] d_to_clk_levm2,
    input logic [7:0] one,
    input logic [7:0] m_from_clk_lev1_r,
    input logic [7:0] n_from_clk_lev2,
    input logic [7:0] o_from_com_levs11,
    input logic [7:0] o_from_comandclk_levs12
);
    // m_from_clk_lev1_r captures (a_to_clk_levm3 + d_to_clk_levm2) + b_to_clk_levm1 on the previous cycle.
    check_m_update_from_inputs: assert property (
        @(posedge clk) m_from_clk_lev1_r == $past((a_to_clk_levm3 + d_to_clk_levm2) + b_to_clk_levm1)
    );

    // n_from_clk_lev2 is a combinational mirror of m_from_clk_lev1_r.
    check_n_mirrors_m: assert property (
        @(posedge clk) n_from_clk_lev2 == m_from_clk_lev1_r
    );

    // o_from_com_levs11 is c_com_levs10 + 1 (8-bit wrap).
    check_o_com_plus1: assert property (
        @(posedge clk) o_from_com_levs11 == (c_com_levs10 + 8'd1)
    );

    // o_from_comandclk_levs12 equals (c_com_levs10 + one) + n_from_clk_lev2 (combinational).
    check_o_andclk_sum_with_n: assert property (
        @(posedge clk) o_from_comandclk_levs12 == ((c_com_levs10 + one) + n_from_clk_lev2)
    );

    // By transitivity (n == m), o_from_comandclk_levs12 also equals (c_com_levs10 + one) + m_from_clk_lev1_r.
    check_o_andclk_sum_with_m: assert property (
        @(posedge clk) o_from_comandclk_levs12 == ((c_com_levs10 + one) + m_from_clk_lev1_r)
    );

    // n_from_clk_lev2 also reflects the registered sum from the previous cycle.
    check_n_update_from_inputs: assert property (
        @(posedge clk) n_from_clk_lev2 == $past((a_to_clk_levm3 + d_to_clk_levm2) + b_to_clk_levm1)
    );

    // If the adder inputs are stable over a cycle, m_from_clk_lev1_r holds its value.
    check_m_holds_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a_to_clk_levm3) && $stable(b_to_clk_levm1) && $stable(d_to_clk_levm2)) |-> (m_from_clk_lev1_r == $past(m_from_clk_lev1_r))
    );

    // If operands to o_from_comandclk_levs12 are stable over a cycle, it holds its value.
    check_o_andclk_holds_when_operands_stable: assert property (
        @(posedge clk) ($stable(c_com_levs10) && $stable(one) && $stable(n_from_clk_lev2)) |-> (o_from_comandclk_levs12 == $past(o_from_comandclk_levs12))
    );

    // Any change on m_from_clk_lev1_r must be reflected on n_from_clk_lev2 at the same clock.
    check_n_changes_with_m: assert property (
        @(posedge clk) $changed(m_from_clk_lev1_r) |-> $changed(n_from_clk_lev2)
    );

    // If m_from_clk_lev1_r does not change across a cycle, n_from_clk_lev2 does not change either.
    check_n_not_change_when_m_not_change: assert property (
        @(posedge clk) !$changed(m_from_clk_lev1_r) |-> !$changed(n_from_clk_lev2)
    );
endmodule