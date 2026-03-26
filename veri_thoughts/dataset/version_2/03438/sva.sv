module DFF_SR_GATED_sva (
    input logic D,
    input logic S,
    input logic R,
    input logic G,
    input logic Q,
    input logic QN
);

    // Reset has priority over set and data on the next gated clock.
    check_reset_priority: assert property (
        @(posedge G) disable iff (1'b0)
        (R == 1'b1) |=> ((Q === 1'b0) && (QN === 1'b1))
    );

    // Set drives Q high when reset is not asserted.
    check_set_action: assert property (
        @(posedge G) disable iff (1'b0)
        ((R == 1'b0) && (S == 1'b1)) |=> ((Q === 1'b1) && (QN === 1'b0))
    );

    // With set and reset low, Q loads D on the next gated clock.
    check_data_load: assert property (
        @(posedge G) disable iff (1'b0)
        ((R == 1'b0) && (S == 1'b0)) |=> ((Q === $past(D)) && (QN === ~$past(D)))
    );

    // QN is always the complement of Q.
    check_qn_complement: assert property (
        @(posedge G) disable iff (1'b0)
        (QN === ~Q)
    );

endmodule