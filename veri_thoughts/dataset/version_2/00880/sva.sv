module pipelined_xor_gate_sva (
    input logic a,
    input logic b,
    input logic out_assign,
    input logic clk
);
    ///// Pipelined XOR behavior /////
    // If a^b is 1 this cycle, out_assign is 1 next cycle.
    check_out_follows_xor_high: assert property (
        @(posedge clk) ((a ^ b) == 1'b1) |=> (out_assign == 1'b1)
    );
    // If a^b is 0 this cycle, out_assign is 0 next cycle.
    check_out_follows_xor_low: assert property (
        @(posedge clk) ((a ^ b) == 1'b0) |=> (out_assign == 1'b0)
    );
endmodule

module pipeline_stage_1_sva (
    input logic a,
    input logic b,
    input logic a_reg,
    input logic b_reg,
    input logic clk
);
    ///// Stage 1 register behavior /////
    // If a is 1 this cycle, a_reg is 1 next cycle.
    check_a_reg_high: assert property (
        @(posedge clk) (a == 1'b1) |=> (a_reg == 1'b1)
    );
    // If a is 0 this cycle, a_reg is 0 next cycle.
    check_a_reg_low: assert property (
        @(posedge clk) (a == 1'b0) |=> (a_reg == 1'b0)
    );
    // If b is 1 this cycle, b_reg is 1 next cycle.
    check_b_reg_high: assert property (
        @(posedge clk) (b == 1'b1) |=> (b_reg == 1'b1)
    );
    // If b is 0 this cycle, b_reg is 0 next cycle.
    check_b_reg_low: assert property (
        @(posedge clk) (b == 1'b0) |=> (b_reg == 1'b0)
    );
endmodule

module pipeline_stage_2_sva (
    input logic xor_out,
    input logic out_assign_reg,
    input logic clk
);
    ///// Stage 2 register behavior /////
    // If xor_out is 1 this cycle, out_assign_reg is 1 next cycle.
    check_out_reg_high: assert property (
        @(posedge clk) (xor_out == 1'b1) |=> (out_assign_reg == 1'b1)
    );
    // If xor_out is 0 this cycle, out_assign_reg is 0 next cycle.
    check_out_reg_low: assert property (
        @(posedge clk) (xor_out == 1'b0) |=> (out_assign_reg == 1'b0)
    );
endmodule