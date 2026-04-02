module sky130_fd_sc_lp__ha_sva (
    input logic CLK,
    input logic A,
    input logic B,
    output logic COUT,
    output logic SUM
);
    // COUT is the result of ANDing A and B
    and_result: assert property (
        @(posedge CLK) disable iff (!CLK) (COUT == (A & B))
    );

    // SUM is the result of XORing A and B
    xor_result: assert property (
        @(posedge CLK) disable iff (!CLK) (SUM == (A ^ B))
    );
endmodule