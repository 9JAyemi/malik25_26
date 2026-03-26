module ceespu_compare_sva (
    input logic [31:0] I_dataA,
    input logic [31:0] I_dataB,
    input logic [2:0]  I_branchOp,
    input logic        I_Cin,
    input logic        O_doBranch
);

    // No RTL clock or reset; sample properties on Jasper global clock.

    // Op 0 branches on equality.
    check_branch_eq: assert property (
        @($global_clock)
        (I_branchOp === 3'd0) |-> (O_doBranch === (I_dataA == I_dataB))
    );

    // Op 1 branches on inequality.
    check_branch_ne: assert property (
        @($global_clock)
        (I_branchOp === 3'd1) |-> (O_doBranch === (I_dataA != I_dataB))
    );

    // Op 2 branches on unsigned greater-than.
    check_branch_gt_unsigned: assert property (
        @($global_clock)
        (I_branchOp === 3'd2) |-> (O_doBranch === (I_dataA > I_dataB))
    );

    // Op 3 branches on unsigned greater-than-or-equal.
    check_branch_ge_unsigned: assert property (
        @($global_clock)
        (I_branchOp === 3'd3) |-> (O_doBranch === (I_dataA >= I_dataB))
    );

    // Op 4 branches on signed greater-than.
    check_branch_gt_signed: assert property (
        @($global_clock)
        (I_branchOp === 3'd4) |-> (O_doBranch === ($signed(I_dataA) > $signed(I_dataB)))
    );

    // Op 5 branches on signed greater-than-or-equal.
    check_branch_ge_signed: assert property (
        @($global_clock)
        (I_branchOp === 3'd5) |-> (O_doBranch === ($signed(I_dataA) >= $signed(I_dataB)))
    );

    // Op 6 forwards the carry-in.
    check_branch_cin: assert property (
        @($global_clock)
        (I_branchOp === 3'd6) |-> (O_doBranch === I_Cin)
    );

    // Op 7 always branches.
    check_branch_always: assert property (
        @($global_clock)
        (I_branchOp === 3'd7) |-> (O_doBranch === 1'b1)
    );

    // Stable inputs keep the combinational output stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock)
        (!$initstate &&
         $stable(I_dataA) &&
         $stable(I_dataB) &&
         $stable(I_branchOp) &&
         $stable(I_Cin)) |-> $stable(O_doBranch)
    );

    // For ops that do not use I_Cin, changing only I_Cin does not change the output.
    check_cin_irrelevant_for_non_cin_ops: assert property (
        @($global_clock)
        (!$initstate &&
         ((I_branchOp === 3'd0) ||
          (I_branchOp === 3'd1) ||
          (I_branchOp === 3'd2) ||
          (I_branchOp === 3'd3) ||
          (I_branchOp === 3'd4) ||
          (I_branchOp === 3'd5) ||
          (I_branchOp === 3'd7)) &&
         $stable(I_dataA) &&
         $stable(I_dataB) &&
         $stable(I_branchOp) &&
         !$stable(I_Cin)) |-> $stable(O_doBranch)
    );

    // In the carry-in op, data changes alone do not affect the output.
    check_data_irrelevant_for_cin_op: assert property (
        @($global_clock)
        (!$initstate &&
         (I_branchOp === 3'd6) &&
         $stable(I_branchOp) &&
         $stable(I_Cin) &&
         (!$stable(I_dataA) || !$stable(I_dataB))) |-> $stable(O_doBranch)
    );

endmodule