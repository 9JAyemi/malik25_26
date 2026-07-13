module MUX4X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Z
);

    // Combinational 4:1 mux; RTL has no clock or reset, so clk is the sampling clock.

    // Z matches the RTL sum-of-products equation.
    check_output_matches_sop: assert property (
        @(posedge clk)
        Z == ((A & ~S1 & ~S0) |
              (B & ~S1 &  S0) |
              (C &  S1 & ~S0) |
              (D &  S1 &  S0))
    );

    // Z matches the selected input.
    check_output_matches_selected_input: assert property (
        @(posedge clk)
        Z == (S1 ? (S0 ? D : C) : (S0 ? B : A))
    );

    // When S1S0 is 00, Z routes A.
    check_select_00_routes_a: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Z == A)
    );

    // When S1S0 is 01, Z routes B.
    check_select_01_routes_b: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Z == B)
    );

    // When S1S0 is 10, Z routes C.
    check_select_10_routes_c: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Z == C)
    );

    // When S1S0 is 11, Z routes D.
    check_select_11_routes_d: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Z == D)
    );

endmodule