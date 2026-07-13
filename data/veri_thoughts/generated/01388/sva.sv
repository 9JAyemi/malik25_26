module bitwise_logic_sva (
    input logic A,
    input logic B,
    input logic [1:0] SEL,
    input logic C
);
    // When SEL==00, C equals A & B.
    check_sel00_and: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        (SEL == 2'b00) |-> (C == (A & B))
    );

    // When SEL==01, C equals A | B.
    check_sel01_or: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        (SEL == 2'b01) |-> (C == (A | B))
    );

    // When SEL==10, C equals A ^ B.
    check_sel10_xor: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        (SEL == 2'b10) |-> (C == (A ^ B))
    );

    // When SEL==11, C equals ~A.
    check_sel11_not: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        (SEL == 2'b11) |-> (C == (~A))
    );

    // AND: if A is 0 then C is 0.
    check_and_zero_when_A0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b00) && (A == 1'b0)) |-> (C == 1'b0)
    );

    // AND: if B is 0 then C is 0.
    check_and_zero_when_B0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b00) && (B == 1'b0)) |-> (C == 1'b0)
    );

    // OR: if A is 1 then C is 1.
    check_or_one_when_A1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b01) && (A == 1'b1)) |-> (C == 1'b1)
    );

    // OR: if B is 1 then C is 1.
    check_or_one_when_B1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b01) && (B == 1'b1)) |-> (C == 1'b1)
    );

    // XOR: if A equals B then C is 0.
    check_xor_zero_when_equal: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b10) && (A == B)) |-> (C == 1'b0)
    );

    // XOR: if A differs from B then C is 1.
    check_xor_one_when_diff: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge SEL[0] or negedge SEL[0] or posedge SEL[1] or negedge SEL[1])
        ((SEL == 2'b10) && (A != B)) |-> (C == 1'b1)
    );
endmodule