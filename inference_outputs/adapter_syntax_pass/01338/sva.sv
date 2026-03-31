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
    input logic [7:0]  pc,
    input logic [7:0]  low_sum,
    input logic [7:0]  pc_plus_one
);

    // low_sum is the 8-bit sum of ir_low and rx_low.
    check_low_sum_definition: assert property (
        @(posedge clk) disable iff (!rst_n)
        low_sum == (ir_low + rx_low)
    );

    // pc_plus_one is m_at plus one.
    check_pc_plus_one_definition: assert property (
        @(posedge clk) disable iff (!rst_n)
        pc_plus_one == (m_at + 8'h01)
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

    // pc_plus_one is always one more than m_at.
    check_pc_plus_one_relation: assert property (
        @(posedge clk) disable iff (!rst_n)
        pc_plus_one == (m_at + 8'h01)
    );

    // rat holds its value when load is not asserted.
    check_rat_holds_without_load: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ld_rat == 1'b0) |=> (rat == $past(rat))
    );

    // pc holds its value when load is not asserted.
    check_pc_holds_without_load: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ld_rat == 1'b0) |=> (pc == $past(pc))
    );

    // rat captures low_sum on a load cycle.
    check_rat_loads_low_sum: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ld_rat == 1'b1) |=> (rat == $past(low_sum))
    );

    // pc captures pc_plus_one on a load cycle.
    check_pc_loads_pc_plus_one: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ld_rat == 1'b1) |=> (pc == $past(pc_plus_one))
    );

endmodule