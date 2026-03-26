module delay_element_sva (
    input logic A,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X,
    input logic [31:0] count
);

    // count starts from its declared initial value of zero.
    check_count_initializes_to_zero: assert property (
        @(posedge VPWR) $initstate |-> (count == 32'd0)
    );

    // count increments by one on each clock until it reaches 500.
    check_count_increments_before_500: assert property (
        @(posedge VPWR) disable iff ($initstate)
        ($past(count) < 32'd500) |-> (count == ($past(count) + 32'd1))
    );

    // count holds at 500 once the terminal value is reached.
    check_count_holds_at_500: assert property (
        @(posedge VPWR) disable iff ($initstate)
        ($past(count) == 32'd500) |-> (count == 32'd500)
    );

    // reaching count 500 can only come from 499 or remain at 500.
    check_count_500_has_valid_predecessor: assert property (
        @(posedge VPWR) disable iff ($initstate)
        (count == 32'd500) |-> (($past(count) == 32'd499) || ($past(count) == 32'd500))
    );

    // X is not updated while the previous count was below 500.
    check_x_stable_before_delay_expires: assert property (
        @(posedge VPWR) disable iff ($initstate)
        ($past(count) < 32'd500) |-> (X === $past(X))
    );

    // After count reaches 500, X reflects the previous sampled value of A.
    check_x_captures_a_after_delay_expires: assert property (
        @(posedge VPWR) disable iff ($initstate)
        ($past(count) == 32'd500) |-> (X === $past(A))
    );

    // Any observed change on X requires the previous count to have been 500.
    check_x_changes_only_after_delay_expires: assert property (
        @(posedge VPWR) disable iff ($initstate)
        (X !== $past(X)) |-> ($past(count) == 32'd500)
    );

endmodule