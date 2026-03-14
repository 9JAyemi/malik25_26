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
    // Clock: clk; no reset present
    // Mixed logic: m_from_clk_lev1_r is sequential; others are combinational
    // Key relations: m = reg((a+d)+b); n = m; o_com = c+1; o_cmdclk = (c+one)+n

    // m_from_clk_lev1_r updates each clk to (a_to_clk_levm3 + d_to_clk_levm2 + b_to_clk_levm1) truncated to 8b.
    check_m_from_clk_lev1_r_update_seq: assert property (
        @(posedge clk) !$initstate |-> ( m_from_clk_lev1_r == $past( ((a_to_clk_levm3 + d_to_clk_levm2) + b_to_clk_levm1)[7:0] ) )
    );

    // n_from_clk_lev2 continuously mirrors m_from_clk_lev1_r.
    check_n_from_clk_lev2_mirror_m: assert property (
        @(posedge clk) n_from_clk_lev2 == m_from_clk_lev1_r
    );

    // n_from_clk_lev2 equals the registered sum from prior cycle as well.
    check_n_from_clk_lev2_seq_sum: assert property (
        @(posedge clk) !$initstate |-> ( n_from_clk_lev2 == $past( ((a_to_clk_levm3 + d_to_clk_levm2) + b_to_clk_levm1)[7:0] ) )
    );

    // o_from_com_levs11 equals c_com_levs10 + 1 (8-bit wrap).
    check_o_from_com_levs11_inc1: assert property (
        @(posedge clk) o_from_com_levs11 == ( (c_com_levs10 + 8'd1) [7:0] )
    );

    // o_from_comandclk_levs12 equals (c_com_levs10 + one + n_from_clk_lev2) truncated to 8b.
    check_o_from_comandclk_levs12_expr_n: assert property (
        @(posedge clk) o_from_comandclk_levs12 == ( ((c_com_levs10 + one) + n_from_clk_lev2) [7:0] )
    );

    // o_from_comandclk_levs12 also equals (c_com_levs10 + one + m_from_clk_lev1_r) truncated to 8b.
    check_o_from_comandclk_levs12_expr_m: assert property (
        @(posedge clk) o_from_comandclk_levs12 == ( ((c_com_levs10 + one) + m_from_clk_lev1_r) [7:0] )
    );

    // If n_from_clk_lev2 changes between cycles, m_from_clk_lev1_r must also change.
    check_n_change_implies_m_change: assert property (
        @(posedge clk) (!$initstate && $changed(n_from_clk_lev2)) |-> $changed(m_from_clk_lev1_r)
    );

    // If m_from_clk_lev1_r changes between cycles, n_from_clk_lev2 must also change.
    check_m_change_implies_n_change: assert property (
        @(posedge clk) (!$initstate && $changed(m_from_clk_lev1_r)) |-> $changed(n_from_clk_lev2)
    );

    // If (c_com_levs10, one, n_from_clk_lev2) are stable across a cycle, o_from_comandclk_levs12 must be stable.
    check_o_cmdclk_stable_when_inputs_stable: assert property (
        @(posedge clk) (!$initstate && $stable(c_com_levs10) && $stable(one) && $stable(n_from_clk_lev2)) |-> $stable(o_from_comandclk_levs12)
    );

    // If o_from_comandclk_levs12 changes, at least one of (c_com_levs10, one, n_from_clk_lev2) changed.
    check_o_cmdclk_change_implies_input_change: assert property (
        @(posedge clk) (!$initstate && $changed(o_from_comandclk_levs12)) |-> ($changed(c_com_levs10) || $changed(one) || $changed(n_from_clk_lev2))
    );

    // If c_com_levs10 is stable across a cycle, o_from_com_levs11 must be stable.
    check_o_com_stable_when_c_stable: assert property (
        @(posedge clk) (!$initstate && $stable(c_com_levs10)) |-> $stable(o_from_com_levs11)
    );

    // If o_from_com_levs11 changes, c_com_levs10 must have changed.
    check_o_com_change_implies_c_change: assert property (
        @(posedge clk) (!$initstate && $changed(o_from_com_levs11)) |-> $changed(c_com_levs10)
    );

endmodule