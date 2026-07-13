module mux_2to1_sva (
    input logic clk,
    input logic OUT,
    input logic IN0,
    input logic IN1,
    input logic S0
);

    // OUT must match the implemented mux equation.
    check_mux_boolean_equation: assert property (
        @(posedge clk) (OUT == ((IN0 & ~S0) | (IN1 & S0)))
    );

    // When select is low, OUT must equal IN0.
    check_select_low_path: assert property (
        @(posedge clk) (S0 == 1'b0) |-> (OUT == IN0)
    );

    // When select is high, OUT must equal IN1.
    check_select_high_path: assert property (
        @(posedge clk) (S0 == 1'b1) |-> (OUT == IN1)
    );

    // If both inputs match, OUT must equal that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (IN0 == IN1) |-> (OUT == IN0)
    );

endmodule