module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);
    // ECK equals (E & SE) | (!E & CK).
    check_function_equivalence: assert property (
        @(posedge CK) ECK == ((E & SE) | (!E & CK))
    );

    // When E is 1, ECK equals SE.
    check_eck_eq_se_when_e1: assert property (
        @(posedge CK) (E == 1'b1) |-> (ECK == SE)
    );

    // When E is 0, ECK equals CK.
    check_eck_eq_ck_when_e0: assert property (
        @(posedge CK) (E == 1'b0) |-> (ECK == CK)
    );

    // When SE is 0, ECK equals CK.
    check_eck_eq_ck_when_se0: assert property (
        @(posedge CK) (SE == 1'b0) |-> (ECK == CK)
    );

    // When SE is 1, ECK equals E | CK.
    check_eck_eq_e_or_ck_when_se1: assert property (
        @(posedge CK) (SE == 1'b1) |-> (ECK == (E | CK))
    );

    // When ECK is 0, then (!E & CK) must hold.
    check_zero_implies_not_e_and_ck: assert property (
        @(posedge CK) (ECK == 1'b0) |-> ((!E & CK))
    );

    // When ECK is 1, then (E & SE) or (!E & CK) must hold.
    check_one_implies_e_and_se_or_not_e_and_ck: assert property (
        @(posedge CK) (ECK == 1'b1) |-> ((E & SE) | (!E & CK))
    );

    // If ECK equals CK, then SE must be 0.
    check_se_zero_when_eck_eq_ck: assert property (
        @(posedge CK) (ECK == CK) |-> (SE == 1'b0)
    );

    // If ECK equals SE, then E must be 1.
    check_e_one_when_eck_eq_se: assert property (
        @(posedge CK) (ECK == SE) |-> (E == 1'b1)
    );

    // If ECK equals E | CK, then SE must be 1.
    check_se_one_when_eck_eq_e_or_ck: assert property (
        @(posedge CK) (ECK == (E | CK)) |-> (SE == 1'b1)
    );
endmodule