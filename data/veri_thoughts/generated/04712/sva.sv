module multiplexer_4to1_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic SEL0,
    input logic SEL1,
    input logic [3:0] Y
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // When SEL is 00, Y must equal A.
    check_select_a: assert property (
        @($global_clock) ({SEL1, SEL0} == 2'b00) |-> (Y == A)
    );

    // When SEL is 01, Y must equal B.
    check_select_b: assert property (
        @($global_clock) ({SEL1, SEL0} == 2'b01) |-> (Y == B)
    );

    // When SEL is 10, Y must equal C.
    check_select_c: assert property (
        @($global_clock) ({SEL1, SEL0} == 2'b10) |-> (Y == C)
    );

    // When SEL is 11, Y must equal D.
    check_select_d: assert property (
        @($global_clock) ({SEL1, SEL0} == 2'b11) |-> (Y == D)
    );

endmodule