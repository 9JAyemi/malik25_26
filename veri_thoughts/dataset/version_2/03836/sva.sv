module mux_4to1_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] D,
    input logic [1:0] S,
    input logic [7:0] Y
);

    // Y selects A when S is 00.
    check_select_a: assert property (
        @($global_clock) (S == 2'b00) |-> (Y == A)
    );

    // Y selects B when S is 01.
    check_select_b: assert property (
        @($global_clock) (S == 2'b01) |-> (Y == B)
    );

    // Y selects C when S is 10.
    check_select_c: assert property (
        @($global_clock) (S == 2'b10) |-> (Y == C)
    );

    // Y selects D when S is 11.
    check_select_d: assert property (
        @($global_clock) (S == 2'b11) |-> (Y == D)
    );

    // Y always matches the RTL mux equation.
    check_mux_function: assert property (
        @($global_clock)
        Y == ((S == 2'b00) ? A :
              (S == 2'b01) ? B :
              (S == 2'b10) ? C :
              D)
    );

endmodule