module mux_4to1_en_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic       en,
    input logic [3:0] out
);

    // When disabled, the output is zero.
    check_out_zero_when_disabled: assert property (
        @($global_clock) !en |-> (out == 4'b0000)
    );

    // When enabled and sel is 00, out passes in0.
    check_sel_00_routes_in0: assert property (
        @($global_clock) (en && (sel == 2'b00)) |-> (out == in0)
    );

    // When enabled and sel is 01, out passes in1.
    check_sel_01_routes_in1: assert property (
        @($global_clock) (en && (sel == 2'b01)) |-> (out == in1)
    );

    // When enabled and sel is 10, out passes in2.
    check_sel_10_routes_in2: assert property (
        @($global_clock) (en && (sel == 2'b10)) |-> (out == in2)
    );

    // When enabled and sel is 11, out passes in3.
    check_sel_11_routes_in3: assert property (
        @($global_clock) (en && (sel == 2'b11)) |-> (out == in3)
    );

endmodule