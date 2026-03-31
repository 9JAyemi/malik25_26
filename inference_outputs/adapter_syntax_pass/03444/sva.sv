module Multiplexer_AC__parameterized36_sva (
    input logic [1:0] ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);

    // No RTL clock or reset; sample this combinational mux on the formal global clock.

    // ctrl=00 selects D0.
    check_select_d0: assert property (
        @($global_clock) (ctrl == 2'b00) |-> (S === D0)
    );

    // ctrl=01 selects D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl == 2'b01) |-> (S === D1)
    );

    // ctrl=10 selects D2.
    check_select_d2: assert property (
        @($global_clock) (ctrl == 2'b10) |-> (S === D2)
    );

    // ctrl=11 selects D3.
    check_select_d3: assert property (
        @($global_clock) (ctrl == 2'b11) |-> (S === D3)
    );

    // ctrl values other than 00/01/10/11 drive X.
    check_default_x: assert property (
        @($global_clock)
        ((ctrl !== 2'b00) && (ctrl !== 2'b01) && (ctrl !== 2'b10) && (ctrl !== 2'b11))
        |-> (S === 1'bx)
    );

    // S always matches the mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        S === ((ctrl == 2'b00) ? D0 :
               (ctrl == 2'b01) ? D1 :
               (ctrl == 2'b10) ? D2 :
               (ctrl == 2'b11) ? D3 :
               1'bx)
    );

endmodule