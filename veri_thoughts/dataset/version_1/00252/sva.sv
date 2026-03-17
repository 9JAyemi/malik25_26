module pipelined_xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out,
    input logic a_reg,
    input logic b_reg
);

    // a_reg captures input a on each rising clock edge.
    check_a_reg_captures_a: assert property (
        @(posedge clk) 1'b1 |=> (a_reg == $past(a))
    );

    // b_reg captures input b on each rising clock edge.
    check_b_reg_captures_b: assert property (
        @(posedge clk) 1'b1 |=> (b_reg == $past(b))
    );

    // out updates from the previous cycle's pipeline register values.
    check_out_uses_prior_pipeline_regs: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(a_reg) ^ $past(b_reg)))
    );

    // out equals a XOR b after the two-cycle pipeline latency.
    check_out_matches_inputs_after_two_cycles: assert property (
        @(posedge clk) 1'b1 |=> ##1 (out == ($past(a, 2) ^ $past(b, 2)))
    );

    // Equal inputs produce a low output after the pipeline latency.
    check_equal_inputs_drive_low_after_two_cycles: assert property (
        @(posedge clk) (a == b) |=> ##1 (out == 1'b0)
    );

    // Different inputs produce a high output after the pipeline latency.
    check_different_inputs_drive_high_after_two_cycles: assert property (
        @(posedge clk) (a != b) |=> ##1 (out == 1'b1)
    );

endmodule