module macc_simple_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] Z
);

    // Z equals the previous cycle's accumulator expression.
    check_accumulate_step: assert property (
        @(posedge clk) !$initstate |-> (Z == $past(Z + (A * B)))
    );

    // A zero operand causes the accumulator to hold.
    check_zero_operand_holds: assert property (
        @(posedge clk) (!$initstate && (($past(A) == 8'h00) || ($past(B) == 8'h00))) |-> (Z == $past(Z))
    );

    // A value of 1 on A adds the previous B directly.
    check_a_one_adds_b: assert property (
        @(posedge clk) (!$initstate && ($past(A) == 8'h01)) |-> (Z == $past(Z + B))
    );

    // A value of 1 on B adds the previous A directly.
    check_b_one_adds_a: assert property (
        @(posedge clk) (!$initstate && ($past(B) == 8'h01)) |-> (Z == $past(Z + A))
    );

    // Nonzero operands produce a nonzero increment.
    check_nonzero_operands_change_z: assert property (
        @(posedge clk) (!$initstate && ($past(A) != 8'h00) && ($past(B) != 8'h00)) |-> (Z != $past(Z))
    );

    // 8'hFF times 8'hFF contributes 16'hFE01 on the next cycle.
    check_max_product_step: assert property (
        @(posedge clk) (!$initstate && ($past(A) == 8'hFF) && ($past(B) == 8'hFF)) |-> (Z == ($past(Z) + 16'hFE01))
    );

endmodule