module sky130_fd_sc_lp__a211o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // No clock or reset in RTL; pure combinational. Sample on input edges.

    // At A1 rising edge, X equals (A1&A2)|B1|C1.
    check_func_on_posedge_A1: assert property (
        @(posedge A1) X == ((A1 & A2) | B1 | C1)
    );

    // At A1 falling edge, X equals (A1&A2)|B1|C1.
    check_func_on_negedge_A1: assert property (
        @(negedge A1) X == ((A1 & A2) | B1 | C1)
    );

    // At A2 rising edge, X equals (A1&A2)|B1|C1.
    check_func_on_posedge_A2: assert property (
        @(posedge A2) X == ((A1 & A2) | B1 | C1)
    );

    // At A2 falling edge, X equals (A1&A2)|B1|C1.
    check_func_on_negedge_A2: assert property (
        @(negedge A2) X == ((A1 & A2) | B1 | C1)
    );

    // At B1 rising edge, X equals (A1&A2)|B1|C1.
    check_func_on_posedge_B1: assert property (
        @(posedge B1) X == ((A1 & A2) | B1 | C1)
    );

    // At B1 falling edge, X equals (A1&A2)|B1|C1.
    check_func_on_negedge_B1: assert property (
        @(negedge B1) X == ((A1 & A2) | B1 | C1)
    );

    // At C1 rising edge, X equals (A1&A2)|B1|C1.
    check_func_on_posedge_C1: assert property (
        @(posedge C1) X == ((A1 & A2) | B1 | C1)
    );

    // At C1 falling edge, X equals (A1&A2)|B1|C1.
    check_func_on_negedge_C1: assert property (
        @(negedge C1) X == ((A1 & A2) | B1 | C1)
    );

endmodule