module Mux_3x1_W11_sva (
    input logic [1:0]  ctrl,
    input logic [10:0] D0,
    input logic [10:0] D1,
    input logic [10:0] D2,
    input logic [10:0] S
);

    // No clock or reset exists in the RTL; assertions use the global clock.

    // When ctrl selects D0, the output must match D0.
    check_select_d0: assert property (
        @($global_clock) (ctrl === 2'b00) |-> (S === D0)
    );

    // When ctrl selects D1, the output must match D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl === 2'b01) |-> (S === D1)
    );

    // When ctrl selects D2, the output must match D2.
    check_select_d2: assert property (
        @($global_clock) (ctrl === 2'b10) |-> (S === D2)
    );

    // Any control value outside 00, 01, or 10 must drive zero.
    check_default_zero: assert property (
        @($global_clock) !((ctrl === 2'b00) || (ctrl === 2'b01) || (ctrl === 2'b10)) |-> (S === 11'b0)
    );

    // The output must always implement the full mux function.
    check_mux_function: assert property (
        @($global_clock)
        S === ((ctrl === 2'b00) ? D0 :
               (ctrl === 2'b01) ? D1 :
               (ctrl === 2'b10) ? D2 : 11'b0)
    );

    // If all inputs are stable across samples, the output must remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(ctrl) && $stable(D0) && $stable(D1) && $stable(D2)) |-> $stable(S)
    );

endmodule