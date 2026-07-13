module top_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic op,
    input logic [31:0] result
);
    // DUT has no clock/reset; pure combinational. Sample on CLK, gate with active-low RESETn.
    // op==0 path: result equals a & b.
    check_op0_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (op == 1'b0) |-> (result == (a & b))
    );
    // op==1 path: result equals concatenation of 16-bit ANDs.
    check_op1_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (op == 1'b1) |-> (result == { (a[31:16] & b[31:16]), (a[15:0] & b[15:0]) })
    );
    // Result always equals full 32-bit AND of a and b.
    check_result_matches_full_and: assert property (
        @(posedge CLK) disable iff (!RESETn)
        result == (a & b)
    );
    // Lower 16 bits of result match a[15:0] & b[15:0].
    check_lower_half: assert property (
        @(posedge CLK) disable iff (!RESETn)
        result[15:0] == (a[15:0] & b[15:0])
    );
    // Upper 16 bits of result match a[31:16] & b[31:16].
    check_upper_half: assert property (
        @(posedge CLK) disable iff (!RESETn)
        result[31:16] == (a[31:16] & b[31:16])
    );
    // No result bit may be 1 where a has 0.
    check_mask_a_zero_forces_result_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((result & ~a) == 32'h0)
    );
    // No result bit may be 1 where b has 0.
    check_mask_b_zero_forces_result_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((result & ~b) == 32'h0)
    );
    // If both a and b bits are 1, result bit must be 1.
    check_both_one_implies_result_one: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (((a & b) & ~result) == 32'h0)
    );
    // If a, b, and op are stable, result must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $stable(a) && $stable(b) && $stable(op) |-> $stable(result)
    );
    // Changing op alone does not change result (both paths are equivalent).
    check_op_change_no_effect: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $changed(op) && $stable(a) && $stable(b) |-> $stable(result)
    );
endmodule