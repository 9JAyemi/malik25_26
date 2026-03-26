module Multiplexer_1bit_sva (
    input logic ctrl,
    input logic D0,
    input logic D1,
    input logic S
);

    // Combinational mux with no RTL clock or reset; sample on the formal global clock.

    // When ctrl is low, S must select D0.
    check_select_d0: assert property (
        @($global_clock) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl is high, S must select D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl == 1'b1) |-> (S == D1)
    );

    // S must always match the mux equation.
    check_mux_equation: assert property (
        @($global_clock) S == (ctrl ? D1 : D0)
    );

endmodule