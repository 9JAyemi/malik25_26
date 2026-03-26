module d_latch_reset_sva (
    input logic D,
    input logic GATE_N,
    input logic RESET_B,
    input logic Q
);

    // A low RESET_B on a rising GATE_N edge clears Q.
    check_reset_clears_q: assert property (
        @(posedge GATE_N) !RESET_B |=> (Q == 1'b0)
    );

    // With reset inactive, D=1 on a rising GATE_N edge is captured into Q.
    check_capture_one: assert property (
        @(posedge GATE_N) disable iff (!RESET_B) D |=> (Q == 1'b1)
    );

    // With reset inactive, D=0 on a rising GATE_N edge is captured into Q.
    check_capture_zero: assert property (
        @(posedge GATE_N) disable iff (!RESET_B) !D |=> (Q == 1'b0)
    );

endmodule