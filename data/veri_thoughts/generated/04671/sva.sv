module sky130_fd_sc_lp__dfxtp_lp_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Clock: CLK. Reset: none.
    // Behavior: positive-edge D flip-flop; power pins are unused in this RTL.

    // Q matches the D value sampled on the previous rising edge.
    check_q_captures_previous_d: assert property (
        @(posedge CLK) 1'b1 |=> (Q === $past(D))
    );

    // A sampled low on D is captured into Q on the next rising edge.
    check_capture_zero: assert property (
        @(posedge CLK) (D === 1'b0) |=> (Q === 1'b0)
    );

    // A sampled high on D is captured into Q on the next rising edge.
    check_capture_one: assert property (
        @(posedge CLK) (D === 1'b1) |=> (Q === 1'b1)
    );

endmodule