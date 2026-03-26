module mux_sva #(parameter WIDTH = 1) (
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);

    // When ctrl is exactly 0, S must select D0.
    check_select_d0: assert property (
        @($global_clock) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is not exactly 0, S must select D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl !== 1'b0) |-> (S === D1)
    );

endmodule