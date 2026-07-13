module data_gen_submodule_sva (
    input logic        clk,
    input logic        reset_n,
    input logic [11:0] Data_A,
    input logic [11:0] Data_B,
    input logic [11:0] Data_C,
    input logic [11:0] Data_D,
    input logic [11:0] Data_E,
    input logic [11:0] Data_F,
    input logic [11:0] Data_G,
    input logic [11:0] Data_H
);

    // While reset is asserted, outputs reflect a zeroed buffer and +1 chains.
    check_reset_output_values: assert property (
        @(posedge clk)
        !reset_n |-> ((Data_A == 12'd0) && (Data_B == 12'd1) &&
                      (Data_C == 12'd2) && (Data_D == 12'd3) &&
                      (Data_E == 12'd0) && (Data_F == 12'd1) &&
                      (Data_G == 12'd2) && (Data_H == 12'd3))
    );

    // Data_E is always a duplicate of Data_A.
    check_data_e_matches_data_a: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_E == Data_A)
    );

    // Data_B is always Data_A plus one.
    check_data_b_from_data_a: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_B == (Data_A + 12'd1))
    );

    // Data_C is always Data_B plus one.
    check_data_c_from_data_b: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_C == (Data_B + 12'd1))
    );

    // Data_D is always Data_C plus one.
    check_data_d_from_data_c: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_D == (Data_C + 12'd1))
    );

    // Data_F is always Data_E plus one.
    check_data_f_from_data_e: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_F == (Data_E + 12'd1))
    );

    // Data_G is always Data_F plus one.
    check_data_g_from_data_f: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_G == (Data_F + 12'd1))
    );

    // Data_H is always Data_G plus one.
    check_data_h_from_data_g: assert property (
        @(posedge clk) disable iff (!reset_n)
        (Data_H == (Data_G + 12'd1))
    );

    // Data_A increments by one when the prior value is below 511.
    check_data_a_increments_below_511: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($past(reset_n) && ($past(Data_A) < 12'd511)) |-> (Data_A == ($past(Data_A) + 12'd1))
    );

    // Data_A wraps to zero when the prior value is 511 or higher.
    check_data_a_wraps_at_511_or_more: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($past(reset_n) && ($past(Data_A) >= 12'd511)) |-> (Data_A == 12'd0)
    );

endmodule