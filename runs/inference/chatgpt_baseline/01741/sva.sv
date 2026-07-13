module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);
    // Clock: CK (posedge). Reset: none. Logic: combinational 2:1 mux (E ? SE : CK).

    // ECK implements (E & SE) | (!E & CK).
    check_mux_equation: assert property (
        @(posedge CK) ECK == ((E & SE) | (!E & CK))
    );

    // When E is 1, ECK follows SE.
    check_E_high_selects_SE: assert property (
        @(posedge CK) (E == 1'b1) |-> (ECK == SE)
    );

    // When E is 0, ECK follows CK.
    check_E_low_selects_CK: assert property (
        @(posedge CK) (E == 1'b0) |-> (ECK == CK)
    );

    // If SE equals CK, ECK equals that common value.
    check_equal_inputs_hold: assert property (
        @(posedge CK) (SE == CK) |-> (ECK == CK)
    );

    // If ECK is 1, it must be driven by E&SE or !E&CK.
    check_eck_one_implication: assert property (
        @(posedge CK) (ECK == 1'b1) |-> ((E & SE) | (!E & CK))
    );

    // If ECK is 0, it must be driven by E&!SE or !E&!CK.
    check_eck_zero_implication: assert property (
        @(posedge CK) (ECK == 1'b0) |-> ((E & !SE) | (!E & !CK))
    );
endmodule