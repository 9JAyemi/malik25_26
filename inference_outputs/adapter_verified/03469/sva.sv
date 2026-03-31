module mux_4to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] SEL,
    input logic Y
);

// When SEL==00, Y equals A.
    check_sel00_routes_a: assert property (
        @(posedge clk) (SEL == 2'b00) |-> (Y == A)
    );

// When SEL==01, Y equals B.
    check_sel01_routes_b: assert property (
        @(posedge clk) (SEL == 2'b01) |-> (Y == B)
    );

// When SEL==10, Y equals C.
    check_sel10_routes_c: assert property (
        @(posedge clk) (SEL == 2'b10) |-> (Y == C)
    );

// When SEL==11, Y equals D.
    check_sel11_routes_d: assert property (
        @(posedge clk) (SEL == 2'b11) |-> (Y == D)
    );

// Y always matches the selected input.
    check_mux_function: assert property (
        @(posedge clk) Y == ((SEL == 2'b00) ? A :
                             (SEL == 2'b01) ? B :
                             (SEL == 2'b10) ? C : D)
    );

endmodule
