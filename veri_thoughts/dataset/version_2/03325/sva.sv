module mux_64to1_sva (
    input logic        clk,
    input logic [63:0] in0,
    input logic [63:0] in1,
    input logic [1:0]  sel,
    input logic [63:0] out
);

    // Combinational DUT; clk is only used to sample assertions.

    // sel=00 routes the low 32 bits of in0 and zero-extends the result.
    check_sel_00_routes_in0_low: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == {32'b0, in0[31:0]})
    );

    // sel=01 routes the high 32 bits of in0 and zero-extends the result.
    check_sel_01_routes_in0_high: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == {32'b0, in0[63:32]})
    );

    // sel=10 routes the low 32 bits of in1 and zero-extends the result.
    check_sel_10_routes_in1_low: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == {32'b0, in1[31:0]})
    );

    // sel=11 routes the high 32 bits of in1 and zero-extends the result.
    check_sel_11_routes_in1_high: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == {32'b0, in1[63:32]})
    );

    // The upper 32 bits of out are always zero due to 32-to-64 bit assignment.
    check_upper_half_zero: assert property (
        @(posedge clk) out[63:32] == 32'b0
    );

    // If the inputs and select stay the same, the output must stay the same.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({in0, in1, sel}) |-> $stable(out)
    );

endmodule