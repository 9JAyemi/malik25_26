module lpm_inv_sva #(
    parameter integer lpm_width = 1
) (
    input logic clk,
    input logic [lpm_width-1:0] data,
    input logic [lpm_width-1:0] result
);

    // result matches the bitwise inversion of data.
    check_result_is_inverted_data: assert property (
        @(posedge clk) disable iff (1'b0) result === ~data
    );

    // If data is unchanged between samples, result is unchanged too.
    check_result_stable_when_data_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(data) |-> $stable(result)
    );

endmodule