module top_module_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);
    // Derived carry terms for low 16b adder nibble (bits [3:0]) with cin=0
    let low_c0 = 1'b0;
    let low_c1 = (a[0] & b[0]);
    let low_c2 = (a[1] & b[1]) | ((a[1] | b[1]) & (a[0] & b[0]));
    let low_c3 = (a[2] & b[2]) | ((a[2] | b[2]) & (a[1] & b[1])) | ((a[2] | b[2]) & (a[1] | b[1]) & (a[0] & b[0]));

    // Derived carry terms for high 16b adder nibble (bits [19:16]) with cin=low_c3
    let high_c0 = low_c3;
    let high_c1 = (a[16] & b[16]) | ((a[16] | b[16]) & high_c0);
    let high_c2 = (a[17] & b[17]) | ((a[17] | b[17]) & (a[16] & b[16])) | ((a[17] | b[17]) & (a[16] | b[16]) & high_c0);
    let high_c3 = (a[18] & b[18]) | ((a[18] | b[18]) & (a[17] & b[17])) | ((a[18] | b[18]) & (a[17] | b[17]) & (a[16] & b[16])) | ((a[18] | b[18]) & (a[17] | b[17]) & (a[16] | b[16]) & high_c0);

    // Low adder: sum[12] equals cin (0).
    check_low_sum12_is_zero: assert property (
        @(posedge CLK) sum[12] == 1'b0
    );

    // Low adder: sum[13] equals carry1 from bit0.
    check_low_sum13_is_c1: assert property (
        @(posedge CLK) sum[13] == low_c1
    );

    // Low adder: sum[14] equals carry2 from bits[1:0].
    check_low_sum14_is_c2: assert property (
        @(posedge CLK) sum[14] == low_c2
    );

    // Low adder: sum[15] equals carry3 from bits[2:0].
    check_low_sum15_is_c3: assert property (
        @(posedge CLK) sum[15] == low_c3
    );

    // Low adder: lower 12-bit sum equals a[15:4] + b[15:4] + {c3,c2,c1,c0}.
    check_low_lower12_sum: assert property (
        @(posedge CLK) sum[11:0] == (a[15:4] + b[15:4] + {low_c3, low_c2, low_c1, low_c0})
    );

    // High adder: sum[28] equals cin from low nibble (low_c3).
    check_high_sum28_is_c0: assert property (
        @(posedge CLK) sum[28] == high_c0
    );

    // High adder: sum[29] equals carry1 from bit16 with cin=high_c0.
    check_high_sum29_is_c1: assert property (
        @(posedge CLK) sum[29] == high_c1
    );

    // High adder: sum[30] equals carry2 from bits[17:16] with cin=high_c0.
    check_high_sum30_is_c2: assert property (
        @(posedge CLK) sum[30] == high_c2
    );

    // High adder: sum[31] equals carry3 from bits[18:16] with cin=high_c0.
    check_high_sum31_is_c3: assert property (
        @(posedge CLK) sum[31] == high_c3
    );

    // High adder: upper 12-bit sum equals a[31:20] + b[31:20] + {c3,c2,c1,c0}.
    check_high_upper12_sum: assert property (
        @(posedge CLK) sum[27:16] == (a[31:20] + b[31:20] + {high_c3, high_c2, high_c1, high_c0})
    );

    // Integration: carry bridge from low cout to high cin (sum[15] == sum[28]).
    check_carry_bridge_low_to_high: assert property (
        @(posedge CLK) sum[28] == sum[15]
    );
endmodule