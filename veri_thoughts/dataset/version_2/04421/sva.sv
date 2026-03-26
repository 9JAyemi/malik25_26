module RegisterAnd_sva (
    input logic EN,
    input logic [3:0] D,
    input logic CLK,
    input logic Q_AND
);

    // After the first clock, Q_AND reflects the prior cycle's registered load result.
    check_qand_matches_prior_load: assert property (
        @(posedge CLK) disable iff ($initstate)
        Q_AND == ($past(EN) && ($past(D) == 4'hF))
    );

    // When EN is low, the register clears and Q_AND is low on the next cycle.
    check_clear_when_disabled: assert property (
        @(posedge CLK)
        !EN |=> !Q_AND
    );

    // Loading 4'b1111 makes Q_AND high on the next cycle.
    check_load_all_ones_sets_qand: assert property (
        @(posedge CLK)
        EN && (D == 4'hF) |=> Q_AND
    );

    // Loading any value other than 4'b1111 makes Q_AND low on the next cycle.
    check_load_non_all_ones_clears_qand: assert property (
        @(posedge CLK)
        EN && (D != 4'hF) |=> !Q_AND
    );

endmodule