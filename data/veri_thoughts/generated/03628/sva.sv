module HilbertTransform_sva #(
    parameter n = 4
) (
    input logic clk,
    input logic signed [n-1:0] in_real,
    input logic signed [n-1:0] out_imag
);

    // Stable input samples must produce stable output samples.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) $stable(in_real) |-> $stable(out_imag)
    );

    genvar i;
    generate
        for (i = 0; i < n; i = i + 2) begin : gen_hilbert_pair_checks
            // Even-indexed output bits are forced low.
            check_even_bit_zero: assert property (
                @(posedge clk) out_imag[i] == 1'b0
            );

            if (i + 1 < n) begin : gen_hilbert_odd_checks
                // Odd-indexed output bits match the RTL subtraction.
                check_odd_bit_difference: assert property (
                    @(posedge clk) out_imag[i+1] == (in_real[i] - in_real[i+1])
                );
            end
        end
    endgenerate

endmodule