module sky130_fd_sc_ls__clkinv_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Y is always the logical inverse of A.
    check_inverter_function: assert property (
        @(posedge clk) Y == ~A
    );

    // A low input produces a high output.
    check_low_input_high_output: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b1)
    );

    // A high input produces a low output.
    check_high_input_low_output: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // A rising input causes a falling output.
    check_rise_input_fall_output: assert property (
        @(posedge clk) $rose(A) |-> $fell(Y)
    );

    // A falling input causes a rising output.
    check_fall_input_rise_output: assert property (
        @(posedge clk) $fell(A) |-> $rose(Y)
    );

    // A rising output causes a falling input.
    check_rise_output_fall_input: assert property (
        @(posedge clk) $rose(Y) |-> $fell(A)
    );

    // A falling output causes a rising input.
    check_fall_output_rise_input: assert property (
        @(posedge clk) $fell(Y) |-> $rose(A)
    );

endmodule