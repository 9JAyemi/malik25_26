module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic X,
    input logic A,
    input logic SLEEP_B,
    input logic CLK,
    input logic RESETn
);
    // A can only transition from HIGH to LOW when SLEEP_B is LOW.
    sleep_b_low: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(A) |-> (SLEEP_B == 1'b0)
    );
    // A can only transition from LOW to HIGH when SLEEP_B is HIGH.
    sleep_b_high: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(A) |-> (SLEEP_B == 1'b1)
    );
    // At reset assertion, A must drive LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (A == 1'b0)
    );
endmodule