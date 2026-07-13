module my_inverter_sva (
    input logic Y,
    input logic A
);
    // No clock or reset in DUT; pure combinational inverter: Y = ~A.

    // On A rising edge, Y must equal bitwise NOT of A.
    check_inversion_on_A_posedge: assert property (
        @(posedge A) (Y === ~A)
    );

    // On A falling edge, Y must equal bitwise NOT of A.
    check_inversion_on_A_negedge: assert property (
        @(negedge A) (Y === ~A)
    );

    // On Y rising edge, A must equal bitwise NOT of Y.
    check_inversion_on_Y_posedge: assert property (
        @(posedge Y) (A === ~Y)
    );

    // On Y falling edge, A must equal bitwise NOT of Y.
    check_inversion_on_Y_negedge: assert property (
        @(negedge Y) (A === ~Y)
    );
endmodule