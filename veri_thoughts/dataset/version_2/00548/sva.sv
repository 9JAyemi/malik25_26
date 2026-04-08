module output_select_sva(
    input logic sel,
    input logic [7:0] out1,
    input logic [7:0] out2,
    input logic [7:0] out
);

    // When sel is 0, out must match out1.
    check_select_out1: assert property (
        @($global_clock) (sel === 1'b0) |-> (out === out1)
    );

    // When sel is not 0, out must match out2.
    check_select_out2: assert property (
        @($global_clock) (sel !== 1'b0) |-> (out === out2)
    );

endmodule