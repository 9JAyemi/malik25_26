module mux_2_1_sva (
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

    // If both inputs are equal, output must equal that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // With stable select and selected input, output must remain stable.
    check_stable_when_selected_input_stable: assert property (
        @(posedge clk) ($stable(sel) && (sel == 1'b0) && $stable(a)) |-> $stable(out)
    );

    // With stable select and unselected input, output must remain stable.
    check_stable_when_unselected_input_stable: assert property (
        @(posedge clk) ($stable(sel) && (sel == 1'b1) && $stable(b)) |-> $stable(out)
    );

endmodule