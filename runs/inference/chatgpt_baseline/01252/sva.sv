module inverter_sva (
    input logic I,
    input logic O
);
    // O must be the bitwise NOT of I.
    check_inverter_function: assert property (
        @(posedge I or negedge I) (O == ~I)
    );
    // On O rising edge, I must be 0.
    check_inverter_posedge_O_implies_I0: assert property (
        @(posedge O) (I == 1'b0)
    );
    // On O falling edge, I must be 1.
    check_inverter_negedge_O_implies_I1: assert property (
        @(negedge O) (I == 1'b1)
    );
endmodule

module and_gate_sva (
    input logic A,
    input logic B,
    input logic Y
);
    // Y must equal A & B.
    check_and_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (Y == (A & B))
    );
    // If Y is 1 then both A and B are 1.
    check_and_y1_implies_inputs1: assert property (
        @(posedge Y) (A == 1'b1 && B == 1'b1)
    );
    // If A is 0 then Y must be 0.
    check_and_a0_implies_y0: assert property (
        @(posedge A or negedge A) (A == 1'b0) |-> (Y == 1'b0)
    );
    // If B is 0 then Y must be 0.
    check_and_b0_implies_y0: assert property (
        @(posedge B or negedge B) (B == 1'b0) |-> (Y == 1'b0)
    );
endmodule

module mux_2to1_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Y must equal (~A & S) | (~B & ~S) per RTL.
    check_mux_equation: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
        (Y == ((~A & S) | (~B & ~S)))
    );
    // When S=1, Y must be ~A.
    check_mux_s1_selects_not_a: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
        (S == 1'b1) |-> (Y == ~A)
    );
    // When S=0, Y must be ~B.
    check_mux_s0_selects_not_b: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
        (S == 1'b0) |-> (Y == ~B)
    );
endmodule