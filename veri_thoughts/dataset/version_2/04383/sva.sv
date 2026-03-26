module mux2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // Output must always match the mux expression.
    check_mux_function: assert property (
        @(posedge clk) (y === (sel ? b : a))
    );

    // When select is low, output must follow input a.
    check_select_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (y === a)
    );

    // When select is high, output must follow input b.
    check_select_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (y === b)
    );

    // A rising select must make the output reflect input b.
    check_sel_rise_switches_to_b: assert property (
        @(posedge clk) $rose(sel) |-> (y === b)
    );

    // A falling select must make the output reflect input a.
    check_sel_fall_switches_to_a: assert property (
        @(posedge clk) $fell(sel) |-> (y === a)
    );

endmodule