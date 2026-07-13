module and_logic_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic reset,
    input logic [3:0] C
);

    // During active-high reset, C is forced to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (C == 4'b0000)
    );

    // Outside reset, C matches the bitwise AND of A and B.
    check_and_output_matches_inputs: assert property (
        @(posedge clk) disable iff (reset) (C == (A & B))
    );

endmodule