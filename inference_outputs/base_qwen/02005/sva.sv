```systemverilog
module sky130_fd_sc_lp__iso0p_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic SLEEP,
    output logic X
);
    wire sleepn;

    not not0 (sleepn, SLEEP);
    and and0 (X, A, sleepn);

    ///// Sleep signal inversion /////
    // Sleepn should be the inverse of SLEEP.
    sleep_inversion: assert property (
        @(posedge CLK) disable iff (!RESETn) (SLEEP == 1'b0) |-> (sleepn == 1'b1)
    );
    sleep_inversion_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (SLEEP == 1'b1) |-> (sleepn == 1'b0)
    );

    ///// Output logic /////
    // X should be HIGH when A is HIGH and SLEEPn is HIGH.
    output_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1) && (sleepn == 1'b1) |-> (X == 1'b1)
    );
    // X should be LOW when A is LOW or SLEEPn is LOW.
    output_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0) |-> (X == 1'b0)
    );
    output_low_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (sleepn == 1'b0) |-> (X == 1'b0)
    );

    ///// Device reset /////
    // At reset assertion, X must drive LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (X == 1'b0)
    );
endmodule
```