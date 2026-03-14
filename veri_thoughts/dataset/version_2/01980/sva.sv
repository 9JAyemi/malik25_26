module MUX2x1_8_1_0_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic SEL,
    input logic [7:0] X
);
    // When SEL=0, output equals A.
    check_sel0_routes_A: assert property (
        @(posedge CLK) (SEL == 1'b0) |-> (X == A)
    );
    // When SEL=1, output equals B.
    check_sel1_routes_B: assert property (
        @(posedge CLK) (SEL == 1'b1) |-> (X == B)
    );
    // On SEL rising edge, output selects B.
    check_rose_sel_routes_B: assert property (
        @(posedge CLK) $rose(SEL) |-> (X == B)
    );
    // On SEL falling edge, output selects A.
    check_fell_sel_routes_A: assert property (
        @(posedge CLK) $fell(SEL) |-> (X == A)
    );
    // Output always equals either A or B.
    check_output_is_A_or_B: assert property (
        @(posedge CLK) (X == A) || (X == B)
    );
endmodule

module MUX4x1_8_2_0_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] D,
    input logic [1:0] SEL,
    input logic [7:0] X
);
    // When SEL==00, output equals A.
    check_sel00_routes_A: assert property (
        @(posedge CLK) (SEL == 2'b00) |-> (X == A)
    );
    // When SEL==10, output equals B.
    check_sel10_routes_B: assert property (
        @(posedge CLK) (SEL == 2'b10) |-> (X == B)
    );
    // When SEL==01, output equals C.
    check_sel01_routes_C: assert property (
        @(posedge CLK) (SEL == 2'b01) |-> (X == C)
    );
    // When SEL==11, output equals D.
    check_sel11_routes_D: assert property (
        @(posedge CLK) (SEL == 2'b11) |-> (X == D)
    );
    // When SEL[0]==0, output comes from A or B.
    check_s0_low_from_AB: assert property (
        @(posedge CLK) (SEL[0] == 1'b0) |-> ((X == A) || (X == B))
    );
    // When SEL[0]==1, output comes from C or D.
    check_s0_high_from_CD: assert property (
        @(posedge CLK) (SEL[0] == 1'b1) |-> ((X == C) || (X == D))
    );
    // On SEL[1] rising edge, output selects B if SEL[0]==0 else D.
    check_rose_s1_selects_B_or_D: assert property (
        @(posedge CLK) $rose(SEL[1]) |-> (X == (SEL[0] ? D : B))
    );
    // On SEL[1] falling edge, output selects A if SEL[0]==0 else C.
    check_fell_s1_selects_A_or_C: assert property (
        @(posedge CLK) $fell(SEL[1]) |-> (X == (SEL[0] ? C : A))
    );
endmodule