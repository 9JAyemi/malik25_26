module mux4to1_sva (
    input logic clk,
    input logic [3:0] A0,
    input logic [3:0] A1,
    input logic [3:0] A2,
    input logic [3:0] A3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

    // Y matches A0[0] when select is 00.
    check_select_00: assert property (
        @(posedge clk) ((S1 == 1'b0) && (S0 == 1'b0)) |-> (Y === A0[0])
    );

    // Y matches A1[0] when select is 01.
    check_select_01: assert property (
        @(posedge clk) ((S1 == 1'b0) && (S0 == 1'b1)) |-> (Y === A1[0])
    );

    // Y matches A2[0] when select is 10.
    check_select_10: assert property (
        @(posedge clk) ((S1 == 1'b1) && (S0 == 1'b0)) |-> (Y === A2[0])
    );

    // Y matches A3[0] when select is 11.
    check_select_11: assert property (
        @(posedge clk) ((S1 == 1'b1) && (S0 == 1'b1)) |-> (Y === A3[0])
    );

    // With select held at 00 and A0[0] stable, Y stays stable.
    check_stable_select_00: assert property (
        @(posedge clk)
        !$initstate &&
        (S1 == 1'b0) && (S0 == 1'b0) &&
        $stable({S1, S0, A0[0]})
        |-> $stable(Y)
    );

    // With select held at 01 and A1[0] stable, Y stays stable.
    check_stable_select_01: assert property (
        @(posedge clk)
        !$initstate &&
        (S1 == 1'b0) && (S0 == 1'b1) &&
        $stable({S1, S0, A1[0]})
        |-> $stable(Y)
    );

    // With select held at 10 and A2[0] stable, Y stays stable.
    check_stable_select_10: assert property (
        @(posedge clk)
        !$initstate &&
        (S1 == 1'b1) && (S0 == 1'b0) &&
        $stable({S1, S0, A2[0]})
        |-> $stable(Y)
    );

    // With select held at 11 and A3[0] stable, Y stays stable.
    check_stable_select_11: assert property (
        @(posedge clk)
        !$initstate &&
        (S1 == 1'b1) && (S0 == 1'b1) &&
        $stable({S1, S0, A3[0]})
        |-> $stable(Y)
    );

endmodule