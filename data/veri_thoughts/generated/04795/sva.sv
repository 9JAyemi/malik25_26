module multiplexer_2to1_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // The output matches the RTL case statement for all select values.
    check_mux_function: assert property (
        @($global_clock)
        (out_always === (((sel_b2 === 1'b1) && (sel_b1 === 1'b1)) ? b : a))
    );

    // When both select bits are high, the output routes input b.
    check_select_11_routes_b: assert property (
        @($global_clock)
        ((sel_b2 === 1'b1) && (sel_b1 === 1'b1)) |-> (out_always === b)
    );

    // For all non-11 select values, the default path routes input a.
    check_default_routes_a: assert property (
        @($global_clock)
        !((sel_b2 === 1'b1) && (sel_b1 === 1'b1)) |-> (out_always === a)
    );

endmodule