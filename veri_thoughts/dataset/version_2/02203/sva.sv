module multiplier_sva
    #(parameter int W = 32)
(
    input logic clk,
    input logic [W-1:0] Data_A_i,
    input logic [W-1:0] Data_B_i,
    input logic [2*W-1:0] Data_S_o
);

    // Output equals product of prior-cycle inputs (1-cycle latency).
    check_product_latency: assert property (
        @(posedge clk) $past(1'b1) |-> (Data_S_o == ($past(Data_A_i) * $past(Data_B_i)))
    );

    // If prior A is zero, output must be zero.
    check_zero_if_a_zero: assert property (
        @(posedge clk) $past(1'b1) && ($past(Data_A_i) == {W{1'b0}}) |-> (Data_S_o == {2*W{1'b0}})
    );

    // If prior B is zero, output must be zero.
    check_zero_if_b_zero: assert property (
        @(posedge clk) $past(1'b1) && ($past(Data_B_i) == {W{1'b0}}) |-> (Data_S_o == {2*W{1'b0}})
    );

    // If prior A is 1, output equals zero-extended prior B.
    check_identity_if_a_one: assert property (
        @(posedge clk) $past(1'b1) && ($past(Data_A_i) == {{(W-1){1'b0}},1'b1}) |-> (Data_S_o == {{W{1'b0}}, $past(Data_B_i)})
    );

    // If prior B is 1, output equals zero-extended prior A.
    check_identity_if_b_one: assert property (
        @(posedge clk) $past(1'b1) && ($past(Data_B_i) == {{(W-1){1'b0}},1'b1}) |-> (Data_S_o == {{W{1'b0}}, $past(Data_A_i)})
    );

    // LSB of output equals AND of prior-cycle input LSBs.
    check_lsb_and: assert property (
        @(posedge clk) $past(1'b1) |-> (Data_S_o[0] == ($past(Data_A_i[0]) & $past(Data_B_i[0])))
    );

    // If both prior inputs are odd, output LSB is 1.
    check_lsb_one_if_both_odd: assert property (
        @(posedge clk) $past(1'b1) && $past(Data_A_i[0]) && $past(Data_B_i[0]) |-> (Data_S_o[0] == 1'b1)
    );

    // If either prior input is even, output LSB is 0.
    check_lsb_zero_if_either_even: assert property (
        @(posedge clk) $past(1'b1) && ((!$past(Data_A_i[0])) || (!$past(Data_B_i[0]))) |-> (Data_S_o[0] == 1'b0)
    );

    // If inputs are unchanged across two cycles, output is unchanged across one cycle.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $past(1'b1,2) && ($past(Data_A_i,1) == $past(Data_A_i,2)) && ($past(Data_B_i,1) == $past(Data_B_i,2)) |-> (Data_S_o == $past(Data_S_o,1))
    );

    // If prior A == 2, output equals zero-extended prior B shifted left by 1.
    generate if (W >= 2) begin : gen_shift_by1
        check_a_eq2_shift_b: assert property (
            @(posedge clk) $past(1'b1) && ($past(Data_A_i) == {{(W-2){1'b0}}, 2'b10}) |-> (Data_S_o == ({{W{1'b0}}, $past(Data_B_i)} << 1))
        );
        // If prior B == 2, output equals zero-extended prior A shifted left by 1.
        check_b_eq2_shift_a: assert property (
            @(posedge clk) $past(1'b1) && ($past(Data_B_i) == {{(W-2){1'b0}}, 2'b10}) |-> (Data_S_o == ({{W{1'b0}}, $past(Data_A_i)} << 1))
        );
    end endgenerate

endmodule