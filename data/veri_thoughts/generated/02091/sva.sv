module priority_encoder_sva (
    input logic clk,
    input logic [7:0] D,
    input logic [2:0] EN
);
    // EN matches the combinational function of D[7:5].
    check_function_equivalence: assert property (
        @(posedge clk) EN == { (D[7] && !D[6] && !D[5]),
                               (!D[7] && D[6] && !D[5]),
                               (!D[7] && !D[6] && D[5]) }
    );

    // EN is one-hot or zero at all times.
    check_en_is_onehot0: assert property (
        @(posedge clk) $onehot0(EN)
    );

    // If none of D[7:5] are HIGH, EN must be 000.
    check_none_high_results_zero: assert property (
        @(posedge clk) (D[7:5] == 3'b000) |-> (EN == 3'b000)
    );

    // If exactly one of D[7:5] is HIGH, EN mirrors D[7:5].
    check_onehot_maps_directly: assert property (
        @(posedge clk) $onehot(D[7:5]) |-> (EN == D[7:5])
    );

    // If two or more of D[7:5] are HIGH, EN must be 000.
    check_multi_high_results_zero: assert property (
        @(posedge clk) ((D[7] & D[6]) | (D[7] & D[5]) | (D[6] & D[5])) |-> (EN == 3'b000)
    );

    // EN[2]==1 implies D7=1, D6=0, D5=0.
    check_en2_implies_d7_only: assert property (
        @(posedge clk) EN[2] |-> (D[7] && !D[6] && !D[5])
    );

    // EN[1]==1 implies D6=1, D7=0, D5=0.
    check_en1_implies_d6_only: assert property (
        @(posedge clk) EN[1] |-> (!D[7] && D[6] && !D[5])
    );

    // EN[0]==1 implies D5=1, D7=0, D6=0.
    check_en0_implies_d5_only: assert property (
        @(posedge clk) EN[0] |-> (!D[7] && !D[6] && D[5])
    );
endmodule