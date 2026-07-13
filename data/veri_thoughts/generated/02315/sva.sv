module comparator_16bit_sva (
    input logic clk,
    input logic reset_n,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic lt,
    input logic eq,
    input logic gt
);
    // lt must reflect (a < b).
    check_lt_definition: assert property (
        @(posedge clk) disable iff (!reset_n) lt == (a < b)
    );

    // eq must reflect (a == b).
    check_eq_definition: assert property (
        @(posedge clk) disable iff (!reset_n) eq == (a == b)
    );

    // gt must reflect (a > b).
    check_gt_definition: assert property (
        @(posedge clk) disable iff (!reset_n) gt == (a > b)
    );

    // Exactly one of lt/eq/gt must be HIGH.
    check_onehot_outputs: assert property (
        @(posedge clk) disable iff (!reset_n) $onehot({lt, eq, gt})
    );

    // At least one of lt/eq/gt must be HIGH.
    check_outputs_complete: assert property (
        @(posedge clk) disable iff (!reset_n) (lt || eq || gt)
    );

    // No two outputs can be HIGH simultaneously.
    check_outputs_mutex: assert property (
        @(posedge clk) disable iff (!reset_n) !(lt && eq) && !(lt && gt) && !(eq && gt)
    );

    // If a and b are stable, outputs must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset_n) ($stable(a) && $stable(b)) |-> ($stable(lt) && $stable(eq) && $stable(gt))
    );

    // Outputs can change only if a or b changes.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) disable iff (!reset_n) ($changed(lt) || $changed(eq) || $changed(gt)) |-> ($changed(a) || $changed(b))
    );
endmodule