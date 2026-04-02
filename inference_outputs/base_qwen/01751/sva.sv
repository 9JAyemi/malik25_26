module c_clkgate_sva (
    input logic clk,
    input logic active,
    output logic clk_gated
);
    // Sequential logic to ensure active_q is updated on the rising edge of clk
    seq_update_active_q: assert property (
        @(posedge clk) disable iff (!active) active_q == active
    );
    
    // Combinational logic to ensure clk_gated is updated on the rising edge of clk
    comb_clk_gated: assert property (
        @(posedge clk) disable iff (!active) clk_gated == (clk & active_q)
    );
    
    // Ensure active_q is updated only on the rising edge of clk
    seq_active_q_update: assert property (
        @(posedge clk) disable iff (!active) $stable(active_q)
    );
    
    // Ensure clk_gated is updated only on the rising edge of clk
    seq_clk_gated_update: assert property (
        @(posedge clk) disable iff (!active) $stable(clk_gated)
    );
    
    // Ensure active_q is updated only when clk is high
    seq_active_q_clk_check: assert property (
        @(posedge clk) disable iff (!active) clk == 1'b1
    );
    
    // Ensure clk_gated is updated only when clk is high
    seq_clk_gated_clk_check: assert property (
        @(posedge clk) disable iff (!active) clk == 1'b1
    );
    
    // Ensure active_q is updated only when active is high
    seq_active_q_active_check: assert property (
        @(posedge clk) disable iff (!active) active == 1'b1
    );
    
    // Ensure clk_gated is updated only when active is high
    seq_clk_gated_active_check: assert property (
        @(posedge clk) disable iff (!active) active == 1'b1
    );
    
    // Ensure active_q is updated only when clk is high and active is high
    seq_active_q_clk_active_check: assert property (
        @(posedge clk) disable iff (!active) (clk == 1'b1) && (active == 1'b1)
    );
    
    // Ensure clk_gated is updated only when clk is high and active is high
    seq_clk_gated_clk_active_check: assert property (
        @(posedge clk) disable iff (!active) (clk == 1'b1) && (active == 1'b1)
    );
endmodule