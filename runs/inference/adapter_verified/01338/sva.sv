module dpth_addr_sva (
    input logic        clk,
    input logic        rst_n,
    input logic [7:0]  ir_low,
    input logic [7:0]  rx_low,
    input logic        ld_rat,
    input logic        ld_pc,
    input logic        pc_at,
    input logic [7:0]  m_at,
    input logic [7:0]  rat,
    input logic [7:0]  pc
);

// Reset clears both registers and the output selector.
    check_reset_clears_state: assert property (
        @(posedge clk) !rst_n |-> ((rat == 8'h00) && (pc == 8'h00) && (m_at == 8'h00))
    );

// ld_rat captures the low-sum into rat on the next cycle.
    check_rat_load_from_low_sum: assert property (
        @(posedge clk) disable iff (!rst_n)
        ld_rat |=> (rat == ($past(ir_low) + $past(rx_low)))
    );

// ld_rat captures pc+1 into pc on the next cycle.
    check_pc_load_from_pc_plus_one: assert property (
        @(posedge clk) disable iff (!rst_n)
        ld_rat |=> (pc == ($past(m_at) + 8'h01))
    );

// ld_rat has priority over ld_pc when both are asserted.
    check_rat_priority_over_pc: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ld_rat && ld_pc) |=> ((rat == ($past(ir_low) + $past(rx_low))) && (pc == ($past(m_at) + 8'h01)))
    );

// m_at selects pc when pc_at is low.
    check_m_at_selects_pc: assert property (
        @(posedge clk) disable iff (!rst_n)
        (pc_at == 1'b0) |-> (m_at == pc)
    );

// m_at selects rat when pc_at is high.
    check_m_at_selects_rat: assert property (
        @(posedge clk) disable iff (!rst_n)
        (pc_at == 1'b1) |-> (m_at == rat)
    );

// m_at matches the RTL sum of pc_at and the previous cycle's output.
    check_m_at_matches_mux: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |-> (m_at == (($past(pc_at) ? $past(rat) : $past(pc)) + 8'h01))
    );

endmodule
