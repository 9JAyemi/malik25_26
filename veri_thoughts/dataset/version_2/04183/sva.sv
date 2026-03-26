module counter_assertions (
    input logic       iCLK,
    input logic       iRST,
    input logic [3:0] oCNT
);

    // Reset drives the counter to zero by the next sampled clock edge.
    check_reset_clears_count: assert property (
        @(posedge iCLK) iRST |=> (oCNT == 4'h0)
    );

    // The visible count is zero on the first cycle after reset deasserts.
    check_reset_release_count_zero: assert property (
        @(posedge iCLK) disable iff (iRST) $fell(iRST) |-> (oCNT == 4'h0)
    );

    // When active and below 15, the counter increments by one each cycle.
    check_counter_increments: assert property (
        @(posedge iCLK) disable iff (iRST)
        (oCNT != 4'hF) |=> (oCNT == ($past(oCNT) + 4'h1))
    );

    // When active at 15, the 4-bit counter wraps back to zero.
    check_counter_wraps_to_zero: assert property (
        @(posedge iCLK) disable iff (iRST)
        (oCNT == 4'hF) |=> (oCNT == 4'h0)
    );

endmodule