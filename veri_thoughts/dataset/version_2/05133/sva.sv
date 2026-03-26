module reg3_sync_reset_sva (
    input logic CLK,
    input logic RST,
    input logic [2:0] D,
    input logic [2:0] Q
);

    // Reset clears Q on the following clock sample.
    check_reset_clears_q: assert property (
        @(posedge CLK) disable iff ($initstate) RST |=> (Q == 3'b000)
    );

    // Across non-reset cycles, Q captures the prior value of D.
    check_data_capture_between_nonreset_cycles: assert property (
        @(posedge CLK) disable iff (RST) !RST |=> (Q == $past(D))
    );

    // Q always reflects either the prior reset or the prior D sample.
    check_registered_equation: assert property (
        @(posedge CLK) disable iff ($initstate) Q == ($past(RST) ? 3'b000 : $past(D))
    );

endmodule