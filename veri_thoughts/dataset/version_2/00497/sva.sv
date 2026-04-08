module abs_difference_sum_sva (
    input logic [15:0] input_a,
    input logic [15:0] input_b,
    input logic [15:0] output_sum
);

    function automatic [3:0] abs4(input [3:0] x, input [3:0] y);
        begin
            abs4 = (x > y) ? (x - y) : (y - x);
        end
    endfunction

    // Low output nibble uses a-b when the low nibble of a is larger.
    check_low_nibble_gt_branch: assert property (
        @($global_clock)
        (input_a[3:0] > input_b[3:0]) |-> (output_sum[3:0] == (input_a[3:0] - input_b[3:0]))
    );

    // Low output nibble uses b-a when the low nibble of b is larger or equal.
    check_low_nibble_le_branch: assert property (
        @($global_clock)
        (input_a[3:0] <= input_b[3:0]) |-> (output_sum[3:0] == (input_b[3:0] - input_a[3:0]))
    );

    // Bits [7:4] use a-b when that nibble of a is larger.
    check_midlow_nibble_gt_branch: assert property (
        @($global_clock)
        (input_a[7:4] > input_b[7:4]) |-> (output_sum[7:4] == (input_a[7:4] - input_b[7:4]))
    );

    // Bits [7:4] use b-a when that nibble of b is larger or equal.
    check_midlow_nibble_le_branch: assert property (
        @($global_clock)
        (input_a[7:4] <= input_b[7:4]) |-> (output_sum[7:4] == (input_b[7:4] - input_a[7:4]))
    );

    // Bits [11:8] use a-b when that nibble of a is larger.
    check_midhigh_nibble_gt_branch: assert property (
        @($global_clock)
        (input_a[11:8] > input_b[11:8]) |-> (output_sum[11:8] == (input_a[11:8] - input_b[11:8]))
    );

    // Bits [11:8] use b-a when that nibble of b is larger or equal.
    check_midhigh_nibble_le_branch: assert property (
        @($global_clock)
        (input_a[11:8] <= input_b[11:8]) |-> (output_sum[11:8] == (input_b[11:8] - input_a[11:8]))
    );

    // High output nibble uses a-b when the high nibble of a is larger.
    check_high_nibble_gt_branch: assert property (
        @($global_clock)
        (input_a[15:12] > input_b[15:12]) |-> (output_sum[15:12] == (input_a[15:12] - input_b[15:12]))
    );

    // High output nibble uses b-a when the high nibble of b is larger or equal.
    check_high_nibble_le_branch: assert property (
        @($global_clock)
        (input_a[15:12] <= input_b[15:12]) |-> (output_sum[15:12] == (input_b[15:12] - input_a[15:12]))
    );

    // The 16-bit output is the concatenation of the four nibble absolute differences.
    check_output_concatenation: assert property (
        @($global_clock)
        output_sum == {
            abs4(input_a[15:12], input_b[15:12]),
            abs4(input_a[11:8],  input_b[11:8]),
            abs4(input_a[7:4],   input_b[7:4]),
            abs4(input_a[3:0],   input_b[3:0])
        }
    );

    // Identical input words produce an all-zero output word.
    check_equal_inputs_zero_output: assert property (
        @($global_clock)
        (input_a == input_b) |-> (output_sum == 16'h0000)
    );

endmodule