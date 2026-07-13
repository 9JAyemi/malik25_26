module mux_assertions (
    input logic [3:0] opA,
    input logic [3:0] opB,
    input logic [4:0] sum,
    input logic [1:0] dsp_sel,
    input logic [3:0] out
);

    // No reset is present in this RTL.

    // When dsp_sel selects sum, out matches sum[3:0].
    check_select_sum: assert property (
        @($global_clock) (dsp_sel == 2'b00) |-> (out == sum[3:0])
    );

    // When dsp_sel selects cout, out[0] matches sum[4].
    check_select_cout_lsb: assert property (
        @($global_clock) (dsp_sel == 2'b01) |-> (out[0] == sum[4])
    );

    // When dsp_sel selects cout, the upper output bits are zero.
    check_select_cout_upper_zero: assert property (
        @($global_clock) (dsp_sel == 2'b01) |-> (out[3:1] == 3'b000)
    );

    // When dsp_sel selects opB, out matches opB.
    check_select_opb: assert property (
        @($global_clock) (dsp_sel == 2'b10) |-> (out == opB)
    );

    // When dsp_sel selects opA, out matches opA.
    check_select_opa: assert property (
        @($global_clock) (dsp_sel == 2'b11) |-> (out == opA)
    );

endmodule