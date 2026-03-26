module MUX2to1_sva (
    input logic clk,
    input logic data0,
    input logic data1,
    input logic sel,
    input logic out
);

    // Output must implement the mux equation.
    check_mux_equation: assert property (
        @(posedge clk) out == ((data0 & ~sel) | (data1 & sel))
    );

    // When select is low, output must follow data0.
    check_select_low: assert property (
        @(posedge clk) !sel |-> (out == data0)
    );

    // When select is high, output must follow data1.
    check_select_high: assert property (
        @(posedge clk) sel |-> (out == data1)
    );

    // If both inputs are low, output must be low.
    check_both_inputs_low: assert property (
        @(posedge clk) (!data0 && !data1) |-> !out
    );

    // If both inputs are high, output must be high.
    check_both_inputs_high: assert property (
        @(posedge clk) (data0 && data1) |-> out
    );

endmodule