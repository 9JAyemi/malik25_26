module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Y must always be the logical inverse of A.
    check_inverter_function: assert property (
        @(posedge clk) Y == ~A
    );

    // A low input must produce a high output.
    check_low_input_high_output: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b1)
    );

    // A high input must produce a low output.
    check_high_input_low_output: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // A rising input must produce a falling output.
    check_rise_input_fall_output: assert property (
        @(posedge clk) $rose(A) |-> $fell(Y)
    );

    // A falling input must produce a rising output.
    check_fall_input_rise_output: assert property (
        @(posedge clk) $fell(A) |-> $rose(Y)
    );

    // A high output must come from a low input.
    check_high_output_low_input: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A == 1'b0)
    );

    // A low output must come from a high input.
    check_low_output_high_input: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A == 1'b1)
    );

endmodule