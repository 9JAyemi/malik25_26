module top_module_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);
    // Sum equals 32-bit addition of a and b.
    check_sum_matches_add: assert property (
        @(posedge CLK) sum == (a + b)
    );

    // Lower 16 bits equal 16-bit addition of a[15:0] and b[15:0].
    check_lower_half_matches_add: assert property (
        @(posedge CLK) sum[15:0] == (a[15:0] + b[15:0])
    );

    // Upper 16 bits equal 16-bit addition of a[31:16] and b[31:16].
    check_upper_half_matches_add: assert property (
        @(posedge CLK) sum[31:16] == (a[31:16] + b[31:16])
    );

    // If a[15:0] and b[15:0] are zero, lower half is zero.
    check_lower_zero_when_inputs_zero: assert property (
        @(posedge CLK) (a[15:0] == 16'h0000 && b[15:0] == 16'h0000) |-> (sum[15:0] == 16'h0000)
    );

    // If a[31:16] and b[31:16] are zero, upper half is zero.
    check_upper_zero_when_inputs_zero: assert property (
        @(posedge CLK) (a[31:16] == 16'h0000 && b[31:16] == 16'h0000) |-> (sum[31:16] == 16'h0000)
    );

    // If a[15:0] and b[15:0] are all ones, lower half is all ones.
    check_lower_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[15:0] == 16'hFFFF && b[15:0] == 16'hFFFF) |-> (sum[15:0] == 16'hFFFF)
    );

    // If a[31:16] and b[31:16] are all ones, upper half is all ones.
    check_upper_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[31:16] == 16'hFFFF && b[31:16] == 16'hFFFF) |-> (sum[31:16] == 16'hFFFF)
    );

    // If a[15:0] and b[15:0] are all ones, lower half is all ones.
    check_lower_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[15:0] == 16'hFFFF && b[15:0] == 16'hFFFF) |-> (sum[15:0] == 16'hFFFF)
    );

    // If a[31:16] and b[31:16] are all ones, upper half is all ones.
    check_upper_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[31:16] == 16'hFFFF && b[31:16] == 16'hFFFF) |-> (sum[31:16] == 16'hFFFF)
    );

    // If a[15:0] and b[15:0] are zero, lower half is zero.
    check_lower_zero_when_inputs_zero: assert property (
        @(posedge CLK) (a[15:0] == 16'h0000 && b[15:0] == 16'h0000) |-> (sum[15:0] == 16'h0000)
    );

    // If a[31:16] and b[31:16] are zero, upper half is zero.
    check_upper_zero_when_inputs_zero: assert property (
        @(posedge CLK) (a[31:16] == 16'h0000 && b[31:16] == 16'h0000) |-> (sum[31:16] == 16'h0000)
    );

    // If a[15:0] and b[15:0] are all ones, lower half is all ones.
    check_lower_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[15:0] == 16'hFFFF && b[15:0] == 16'hFFFF) |-> (sum[15:0] == 16'hFFFF)
    );

    // If a[31:16] and b[31:16] are all ones, upper half is all ones.
    check_upper_all_ones_when_inputs_all_ones: assert property (
        @(posedge CLK) (a[31:16] == 16'hFFFF && b[31:16] == 16'hFFFF) |-> (sum[31:16] == 16'hFFFF)
    );
endmodule