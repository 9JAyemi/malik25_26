module digital_circuit_sva (
    input logic D,
    input logic Q,
    input logic RESET_B,
    input logic GATE
);

    // Reset sampled low clears Q.
    check_reset_clears_q: assert property (
        @(posedge GATE) (!RESET_B) |=> (Q == 1'b0)
    );

    // Outside reset, Q reflects the D sampled on the prior GATE edge.
    check_data_capture: assert property (
        @(posedge GATE) disable iff (!RESET_B) 1'b1 |=> (Q == $past(D))
    );

    // A sampled high D is captured into Q.
    check_capture_high: assert property (
        @(posedge GATE) disable iff (!RESET_B) (D == 1'b1) |=> (Q == 1'b1)
    );

    // A sampled low D is captured into Q.
    check_capture_low: assert property (
        @(posedge GATE) disable iff (!RESET_B) (D == 1'b0) |=> (Q == 1'b0)
    );

endmodule