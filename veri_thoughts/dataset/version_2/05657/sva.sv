module dff_async_reset_sva (
    input logic D,
    input logic CLK,
    input logic RESET,
    input logic Q
);

    // Q must be low on clock edges while reset is asserted.
    check_q_low_during_reset: assert property (
        @(posedge CLK) RESET |-> (Q == 1'b0)
    );

    // A reset assertion clears Q by the next observed edge.
    check_reset_clears_q: assert property (
        @(posedge CLK or posedge RESET) $rose(RESET) |=> (Q == 1'b0)
    );

    // With no intervening reset, D=1 is captured into Q on the next clock edge.
    check_capture_one: assert property (
        @(posedge CLK or posedge RESET) disable iff (RESET) D |=> (Q == 1'b1)
    );

    // With no intervening reset, D=0 is captured into Q on the next clock edge.
    check_capture_zero: assert property (
        @(posedge CLK or posedge RESET) disable iff (RESET) !D |=> (Q == 1'b0)
    );

endmodule