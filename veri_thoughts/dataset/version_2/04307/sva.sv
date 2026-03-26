module inv_assertions #(
    parameter integer lpm_width = 1,
    parameter lpm_type = "lpm_inv",
    parameter lpm_hint = "UNUSED"
) (
    input logic clk,
    input logic [lpm_width-1:0] data,
    input logic [lpm_width-1:0] result
);

    // Result matches the bitwise inversion of the current input.
    check_result_is_bitwise_inverse: assert property (
        @(posedge clk) result === ~data
    );

    // If the sampled input is unchanged, the sampled output is also unchanged.
    check_stable_input_gives_stable_output: assert property (
        @(posedge clk) $stable(data) |-> $stable(result)
    );

endmodule