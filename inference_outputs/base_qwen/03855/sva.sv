module sky130_fd_sc_ls__clkinv_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    output logic Y
);
    // The output Y is the inverted version of the input A.
    invert_check: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~A
    );
endmodule