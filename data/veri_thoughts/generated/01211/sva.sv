module c17_sva (
    input logic clk,        // Sampling clock for assertions (DUT has no clock/reset)
    input logic N1, N2, N3, N6, N7,
    input logic N22, N23
);
    // Combinational DUT: no reset; outputs are pure functions of inputs.
    // N22 depends on N1,N2,N3,N6; N23 depends on N2,N3,N6,N7.

    // N22 equals its combinational definition from primary inputs.
    check_n22_functional_eq: assert property (
        @(posedge clk) disable iff (1'b0)
        N22 === ~( (~(N1 & N3)) & (~(N2 & (~(N3 & N6)))) )
    );

    // N23 equals its combinational definition from primary inputs.
    check_n23_functional_eq: assert property (
        @(posedge clk) disable iff (1'b0)
        N23 === ~( (~(N2 & (~(N3 & N6)))) & (~((~(N3 & N6)) & N7)) )
    );

    // If N1 and N3 are both 1 then N22 must be 1 (since N10=0).
    check_n22_high_when_n1_and_n3: assert property (
        @(posedge clk) disable iff (1'b0)
        (N1 & N3) |-> (N22 == 1'b1)
    );

    // When N2 is 0, N22 reduces to N1 & N3.
    check_n22_eq_when_n2_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (N2 == 1'b0) |-> (N22 === (N1 & N3))
    );

    // When N3 is 0, N22 reduces to N2.
    check_n22_eq_when_n3_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (N3 == 1'b0) |-> (N22 === N2)
    );

    // When N3=1 and N6=0, N22 reduces to N1 | N2.
    check_n22_eq_when_n3_and_n6_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (N3 == 1'b1 && N6 == 1'b0) |-> (N22 === (N1 | N2))
    );

    // If N2=1 and either N3=0 or N6=0 then N23 must be 1 (since N16=0).
    check_n23_high_when_n2_and_not_n3n6: assert property (
        @(posedge clk) disable iff (1'b0)
        (N2 == 1'b1 && ((N3 == 1'b0) || (N6 == 1'b0))) |-> (N23 == 1'b1)
    );

    // If N7=1 and either N3=0 or N6=0 then N23 must be 1 (since N19=0).
    check_n23_high_when_n7_and_not_n3n6: assert property (
        @(posedge clk) disable iff (1'b0)
        (N7 == 1'b1 && ((N3 == 1'b0) || (N6 == 1'b0))) |-> (N23 == 1'b1)
    );

    // If N3=1 and N6=1 then N23 must be 0 (since N16=1 and N19=1).
    check_n23_zero_when_n3_and_n6: assert property (
        @(posedge clk) disable iff (1'b0)
        (N3 == 1'b1 && N6 == 1'b1) |-> (N23 == 1'b0)
    );

    // When N7 is 0, N23 reduces to N2 & ~(N3 & N6).
    check_n23_eq_when_n7_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (N7 == 1'b0) |-> (N23 === (N2 & ~(N3 & N6)))
    );

    // Toggling N7 alone cannot change N22 (N22 independent of N7).
    independence_n22_from_n7: assert property (
        @(posedge clk) disable iff (1'b0)
        ($changed(N7) && $stable({N1,N2,N3,N6})) |-> $stable(N22)
    );

    // Toggling N1 alone cannot change N23 (N23 independent of N1).
    independence_n23_from_n1: assert property (
        @(posedge clk) disable iff (1'b0)
        ($changed(N1) && $stable({N2,N3,N6,N7})) |-> $stable(N23)
    );

endmodule