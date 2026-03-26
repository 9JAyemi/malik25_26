module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic        select,
    input logic [15:0] result
);

    // Multiplier path drives the output when select is high.
    check_multiplier_selected: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (result == (a * b))
    );

    // Add path drives the output when select is low.
    check_add_selected: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (result == {12'b0, (A + B)})
    );

    // Add path zero-extends the 4-bit add/sub result.
    check_add_zero_extended: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (result[15:4] == 12'b0)
    );

    // Add path low nibble matches the 4-bit sum.
    check_add_low_nibble: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (result[3:0] == (A + B))
    );

    // A rising select switches the observed output to the multiplier path.
    check_select_rise_multiplier: assert property (
        @(posedge clk) disable iff (reset)
        $rose(select) |-> (result == (a * b))
    );

    // A falling select switches the observed output to the add path.
    check_select_fall_add: assert property (
        @(posedge clk) disable iff (reset)
        $fell(select) |-> (result == {12'b0, (A + B)})
    );

    // Multiplier input changes do not affect result while add path stays selected.
    check_add_path_ignores_multiplier_inputs: assert property (
        @(posedge clk) disable iff (reset)
        (!select && $stable(select) && $stable(A) && $stable(B) &&
         (!$stable(a) || !$stable(b))) |-> $stable(result)
    );

    // Add input changes do not affect result while multiplier path stays selected.
    check_multiplier_path_ignores_add_inputs: assert property (
        @(posedge clk) disable iff (reset)
        (select && $stable(select) && $stable(a) && $stable(b) &&
         (!$stable(A) || !$stable(B))) |-> $stable(result)
    );

endmodule