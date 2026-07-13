module mux_4to1_enable_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out
);

    // When disabled, the output must be zero.
    check_out_zero_when_disabled: assert property (
        @($global_clock) !en |-> (out == 4'b0000)
    );

    // When enabled and sel is 00, out must equal in0.
    check_sel_00_when_enabled: assert property (
        @($global_clock) (en && (sel == 2'b00)) |-> (out == in0)
    );

    // When enabled and sel is 01, out must equal in1.
    check_sel_01_when_enabled: assert property (
        @($global_clock) (en && (sel == 2'b01)) |-> (out == in1)
    );

    // When enabled and sel is 10, out must equal in2.
    check_sel_10_when_enabled: assert property (
        @($global_clock) (en && (sel == 2'b10)) |-> (out == in2)
    );

    // When enabled and sel is 11, out must equal in3.
    check_sel_11_when_enabled: assert property (
        @($global_clock) (en && (sel == 2'b11)) |-> (out == in3)
    );

    // When enabled and sel is not 00/01/10/11, out must be zero.
    check_default_zero_when_enabled: assert property (
        @($global_clock) (en && (sel != 2'b00) && (sel != 2'b01) && (sel != 2'b10) && (sel != 2'b11)) |-> (out == 4'b0000)
    );

endmodule