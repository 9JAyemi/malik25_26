module add_sub_pipeline_sva (
    input logic        CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        sub,
    input logic [31:0] sum
);
    ///// Functional correctness /////
    // LSB 16-bit sum equals a[15:0] + b[15:0] + sub (low 16 bits).
    check_sum_lsb_correct: assert property (
        @(posedge CLK) sum[15:0] == (a[15:0] + b[15:0] + sub)[15:0]
    );
    // MSB 16-bit sum equals a[31:16] + b[31:16] + sub (low 16 bits).
    check_sum_msb_correct: assert property (
        @(posedge CLK) sum[31:16] == (a[31:16] + b[31:16] + sub)[15:0]
    );
    // Full 32-bit sum is the concatenation of the two independent 16-bit sums.
    check_sum_concat_correct: assert property (
        @(posedge CLK) sum == { (a[31:16] + b[31:16] + sub)[15:0], (a[15:0] + b[15:0] + sub)[15:0] }
    );

    ///// Stability and independence /////
    // If inputs are unchanged, output is unchanged (purely combinational behavior).
    check_sum_stable_if_inputs_stable: assert property (
        @(posedge CLK) (a == $past(a) && b == $past(b) && sub == $past(sub)) |-> (sum == $past(sum))
    );
    // MSB sum is unaffected by changes to LSB inputs when MSB inputs and sub are unchanged.
    check_msb_independent_of_lsb: assert property (
        @(posedge CLK) (a[31:16] == $past(a[31:16]) && b[31:16] == $past(b[31:16]) && sub == $past(sub)) |-> (sum[31:16] == $past(sum[31:16]))
    );
    // LSB sum is unaffected by changes to MSB inputs when LSB inputs and sub are unchanged.
    check_lsb_independent_of_msb: assert property (
        @(posedge CLK) (a[15:0] == $past(a[15:0]) && b[15:0] == $past(b[15:0]) && sub == $past(sub)) |-> (sum[15:0] == $past(sum[15:0]))
    );

    ///// Basic identities /////
    // When b==0 and sub==0, sum equals a.
    check_identity_b_zero_no_cin: assert property (
        @(posedge CLK) (b == 32'h0 && sub == 1'b0) |-> (sum == a)
    );
    // When a==0 and sub==0, sum equals b.
    check_identity_a_zero_no_cin: assert property (
        @(posedge CLK) (a == 32'h0 && sub == 1'b0) |-> (sum == b)
    );
    // When a==0, b==0, and sub==1, sum is 0x0001_0001.
    check_zero_inputs_sub_one: assert property (
        @(posedge CLK) ((a == 32'h0) && (b == 32'h0) && (sub == 1'b1)) |-> (sum == 32'h0001_0001)
    );

    ///// Algebraic properties /////
    // Swapping a and b across cycles (with sub unchanged) leaves sum unchanged (commutativity).
    check_commutativity_swap: assert property (
        @(posedge CLK) (a == $past(b) && b == $past(a) && sub == $past(sub)) |-> (sum == $past(sum))
    );
    // If a and b are stable and sub toggles, sum[0] toggles (±1 on LSB half).
    check_lsb_bit0_toggles_on_sub_toggle: assert property (
        @(posedge CLK) (a == $past(a) && b == $past(b) && (sub != $past(sub))) |-> (sum[0] != $past(sum[0]))
    );
    // If a and b are stable and sub toggles, sum[16] toggles (±1 on MSB half).
    check_msb_bit0_toggles_on_sub_toggle: assert property (
        @(posedge CLK) (a == $past(a) && b == $past(b) && (sub != $past(sub))) |-> (sum[16] != $past(sum[16]))
    );
endmodule