```systemverilog
module mult_select_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    output logic X
);
    // The logic is purely combinational, so we use @(posedge clk) for assertions.

    // The output X is driven by the inputs A1, A2, and B1_N.
    // X = (A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N))
    logic expected_X;
    always_comb begin
        expected_X = (A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N));
    end

    // Check that the output X matches the expected value.
    check_output: assert property (
        @(posedge clk) disable iff (!reset_n) (X == expected_X)
    ) else $error("Output X does not match expected value.");

endmodule
```