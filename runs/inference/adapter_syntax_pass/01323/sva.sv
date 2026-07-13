module Multiplexer_sva #(parameter N=1) (
    input logic ctrl,
    input logic [N-1:0] D0,
    input logic [N-1:0] D1,
    input logic [N-1:0] S
);

    // S must always match the mux equation.
    check_mux_equation: assert property (
        @($global_clock) S === (ctrl ? D1 : D0)
    );

    // When ctrl is low, S must select D0.
    check_select_d0: assert property (
        @($global_clock) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is high, S must select D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl === 1'b1) |-> (S === D1)
    );

    // If both data inputs are equal, S must match that common value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (D0 === D1) |-> (S === D0)
    );

endmodule