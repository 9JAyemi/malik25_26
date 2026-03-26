module pc_sva (
    input logic clk,
    input logic reset,
    input logic SaltoCond,
    input logic signed [31:0] extSigno,
    input logic oZero,
    input logic [31:0] direinstru
);

    // Synchronous reset clears the program counter.
    check_reset_clears_pc: assert property (
        @(posedge clk) reset |=> (direinstru == 32'd0)
    );

    // With no branch request, the program counter increments by 4.
    check_no_branch_request_increments_pc: assert property (
        @(posedge clk) disable iff (reset)
        (!SaltoCond) |=> (direinstru == ($past(direinstru) + 32'd4))
    );

    // A high oZero prevents the conditional branch and keeps the increment-by-4 behavior.
    check_zero_blocks_branch: assert property (
        @(posedge clk) disable iff (reset)
        (SaltoCond && oZero) |=> (direinstru == ($past(direinstru) + 32'd4))
    );

    // A taken conditional branch loads extSigno shifted left by 2.
    check_taken_branch_loads_target: assert property (
        @(posedge clk) disable iff (reset)
        (SaltoCond && !oZero) |=> (direinstru == ($past(extSigno) << 2))
    );

endmodule