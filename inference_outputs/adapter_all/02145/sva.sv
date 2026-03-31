module mux_2_to_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // Output must match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) out == ((sel == 1'b0) ? a : b)
    );

    // When select is low, output must follow input a.
    check_select_low_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When select is high, output must follow input b.
    check_select_high_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    // If both inputs are equal, output must match that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // With select held low and a stable, output must remain stable.
    check_stable_when_select_low_and_a_stable: assert property (
        @(posedge clk) (sel == 1'b0 && $stable(sel) && $stable(a)) |-> $stable(out)
    );

    // With select held high and b stable, output must remain stable.
    check_stable_when_select_high_and_b_stable: assert property (
        @(posedge clk) (sel == 1'b1 && $stable(sel) && $stable(b)) |-> $stable(out)
    );

    // With select held low and a changing, output must change.
    check_output_changes_with_a_when_select_low: assert property (
        @(posedge clk) (sel == 1'b0 && $stable(sel) && $changed(a)) |-> $changed(out)
    );

    // With select held high and b changing, output must change.
    check_output_changes_with_b_when_select_high: assert property (
        @(posedge clk) (sel == 1'b1 && $stable(sel) && $changed(b)) |-> $changed(out)
    );

endmodule