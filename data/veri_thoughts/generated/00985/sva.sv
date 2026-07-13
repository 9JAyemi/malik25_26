module top_module_sva (
    input logic clk,
    input logic reset,       // Synchronous active-high reset
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    // Internal signals from DUT (bind hierarchically)
    input logic [7:0] reg1,
    input logic [7:0] reg2,
    input logic [7:0] diff
);
    ///// Reset behavior /////
    // During reset, registers and outputs are driven to zero.
    reset_clears_state_and_output: assert property (
        @(posedge clk) reset |-> (reg1 == 8'd0) && (reg2 == 8'd0) && (diff == 8'd0) && (q == 8'd0)
    );

    ///// Register load behavior /////
    // reg1 captures d1 on each rising edge when not in reset.
    reg1_loads_d1_on_nonreset: assert property (
        @(posedge clk) disable iff (reset) reg1 == d1
    );
    // reg2 captures d2 on each rising edge when not in reset.
    reg2_loads_d2_on_nonreset: assert property (
        @(posedge clk) disable iff (reset) reg2 == d2
    );

    ///// Combinational datapath wiring /////
    // diff equals reg1 - reg2.
    diff_matches_regs_sub: assert property (
        @(posedge clk) disable iff (reset) diff == (reg1 - reg2)
    );
    // q is directly driven by diff.
    q_matches_diff: assert property (
        @(posedge clk) disable iff (reset) q == diff
    );
    // q equals reg1 - reg2.
    q_matches_regs_sub: assert property (
        @(posedge clk) disable iff (reset) q == (reg1 - reg2)
    );

    ///// Arithmetic identities from the subtraction /////
    // (reg1 - reg2) + reg2 == reg1 (modulo 8-bit).
    add_inverse_consistency: assert property (
        @(posedge clk) disable iff (reset) reg1 == (diff + reg2)
    );
    // If reg1 == reg2 then diff and q must be zero.
    equal_regs_imply_zero_output: assert property (
        @(posedge clk) disable iff (reset) (reg1 == reg2) |-> (diff == 8'd0) && (q == 8'd0)
    );

    ///// Temporal arithmetic consistency /////
    // If reg1 increments by 1 and reg2 holds, diff increments by 1.
    inc_reg1_increases_diff: assert property (
        @(posedge clk) disable iff (reset)
            (reg1 == $past(reg1) + 8'd1 && reg2 == $past(reg2)) |-> (diff == $past(diff) + 8'd1)
    );
    // If reg2 increments by 1 and reg1 holds, diff decrements by 1.
    inc_reg2_decreases_diff: assert property (
        @(posedge clk) disable iff (reset)
            (reg1 == $past(reg1) && reg2 == $past(reg2) + 8'd1) |-> (diff == $past(diff) - 8'd1)
    );
endmodule