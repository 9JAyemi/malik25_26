module mux_4to1_sva (
    input logic [3:0] data_in,
    input logic [1:0] sel,
    input logic       out
);

    // When sel is 2'b00, out must match data_in[0].
    check_select_00: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == data_in[0])
    );

    // When sel is 2'b01, out must match data_in[1].
    check_select_01: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == data_in[1])
    );

    // When sel is 2'b10, out must match data_in[2].
    check_select_10: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == data_in[2])
    );

    // When sel is 2'b11, out must match data_in[3].
    check_select_11: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == data_in[3])
    );

endmodule