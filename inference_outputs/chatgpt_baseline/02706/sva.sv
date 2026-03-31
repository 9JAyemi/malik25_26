module magnitude_comparator_selector_sva (
    input logic CLK, // sampling clock for formal
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [1:0] select,
    input logic [2:0] comparison_result,
    input logic [1:0] input_selected
);

    // If a > b, drive result=a and select=00.
    check_a_gt_b_drives_a_and_sel00: assert property (
        @(posedge CLK) (a > b) |-> (comparison_result == a) && (input_selected == 2'b00)
    );

    // If b > a, drive result=b and select=01.
    check_b_gt_a_drives_b_and_sel01: assert property (
        @(posedge CLK) (b > a) |-> (comparison_result == b) && (input_selected == 2'b01)
    );

    // If a == b, drive result=a and pass through select.
    check_equal_drives_a_and_sel_passthrough: assert property (
        @(posedge CLK) (a == b) |-> (comparison_result == a) && (input_selected == select)
    );

    // Result is always either a or b.
    check_result_is_either_a_or_b: assert property (
        @(posedge CLK) (comparison_result == a) || (comparison_result == b)
    );

    // MSB of input_selected is 1 only when a == b (values 2 or 3 only on equality).
    check_sel_msb_one_only_when_equal: assert property (
        @(posedge CLK) (input_selected[1] == 1'b1) |-> (a == b)
    );

    // When a != b, MSB of input_selected must be 0 (only 00 or 01 allowed).
    check_not_equal_forces_sel_msb_zero: assert property (
        @(posedge CLK) (a != b) |-> (input_selected[1] == 1'b0)
    );

    // If result==b, then b > a and select must be 01.
    check_result_b_implies_b_gt_a_and_sel01: assert property (
        @(posedge CLK) (comparison_result == b) |-> (b > a) && (input_selected == 2'b01)
    );

    // If result==a, then a >= b.
    check_result_a_implies_a_ge_b: assert property (
        @(posedge CLK) (comparison_result == a) |-> (a >= b)
    );

    // When a != b and only select changes, outputs must not change.
    check_select_irrelevant_when_not_equal: assert property (
        @(posedge CLK) (a != b) && $stable(a) && $stable(b) && !$stable(select)
        |-> $stable(comparison_result) && $stable(input_selected)
    );

    // When a == b and only select changes, result stays and input_selected follows select.
    check_select_passthrough_when_equal_changes: assert property (
        @(posedge CLK) (a == b) && $stable(a) && $stable(b) && !$stable(select)
        |-> $stable(comparison_result) && !$stable(input_selected)
    );

endmodule