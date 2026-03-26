module bitwise_and_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out
);

    // Output always equals the bitwise AND of the two inputs.
    check_out_matches_bitwise_and: assert property (
        @(posedge clk) out == (a & b)
    );

    // If the sampled inputs do not change, the sampled output does not change.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

endmodule