```systemverilog
module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    output logic Y
);
    // The logic is purely combinational, so we will use @(posedge CLK) for assertions.

    // The output Y is the inverted version of the input A.
    invert_check: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~A
    );
endmodule
```