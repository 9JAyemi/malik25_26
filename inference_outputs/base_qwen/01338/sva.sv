```systemverilog
module dpth_addr_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] ir_low,
    input logic [7:0] rx_low,
    input logic ld_rat,
    input logic ld_pc,
    input logic pc_at,
    output logic [7:0] m_at
);
    // Sequential logic for rat register update
    seq_rat_update: assert property (
        @(posedge clk) disable iff (!rst_n) ld_rat |-> (rat == ir_low + rx_low)
    ) else $error("rat register update failed");

    // Sequential logic for pc register update
    seq_pc_update: assert property (
        @(posedge clk) disable iff (!rst_n) ld_rat |-> (pc == m_at + 8'b00000001)
    ) else $error("pc register update failed");

    // Combinational logic for m_at assignment
    comb_m_at_assignment: assert property (
        @(posedge clk) disable iff (!rst_n) (m_at == (pc_at == 1'b0) ? pc : rat)
    ) else $error("m_at assignment failed");

    // Reset behavior for rat and pc registers
    reset_behavior: assert property (
        @(posedge clk) !rst_n |-> (rat == 8'b00000000) && (pc == 8'b00000000)
    ) else $error("reset behavior failed");

    // Combinational logic for low_sum calculation
    comb_low_sum: assert property (
        @(posedge clk) disable iff (!rst_n) (low_sum == ir_low + rx_low)
    ) else $error("low_sum calculation failed");

    // Combinational logic for pc_plus_one calculation
    comb_pc_plus_one: assert property (
        @(posedge clk) disable iff (!rst_n) (pc_plus_one == m_at + 8'b00000001)
    ) else $error("pc_plus_one calculation failed");
endmodule
```