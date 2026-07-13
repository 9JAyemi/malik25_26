module sky130_fd_sc_lp__invlp_sva (
    input logic Y,
    input logic A,
    input logic clk
);

    // Y is always the inversion of A.
    check_inverter_function: assert property (
        @(posedge clk) Y === ~A
    );

    // A sampled low must produce Y sampled high.
    check_low_input_high_output: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A sampled high must produce Y sampled low.
    check_high_input_low_output: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

endmodule