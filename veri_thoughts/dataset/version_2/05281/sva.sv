module sky130_fd_sc_lp__inputiso1p_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // SLEEP high forces X low.
    check_sleep_forces_low: assert property (
        @(posedge clk) SLEEP |-> (X == 1'b0)
    );

    // SLEEP low makes X follow A.
    check_awake_passes_input: assert property (
        @(posedge clk) !SLEEP |-> (X == A)
    );

endmodule