module addsub_16bit_sva (
    input logic        clk,
    input logic [15:0] in0,
    input logic [15:0] in1,
    input logic        control,
    input logic [15:0] out
);

    // Sampling clock for this combinational DUT; the RTL has no reset.

    // In add mode, the output is the 16-bit sum of the inputs.
    check_add_mode_result: assert property (
        @(posedge clk) !control |-> (out == (in0 + in1))
    );

    // In subtract mode, the output is the 16-bit difference of the inputs.
    check_sub_mode_result: assert property (
        @(posedge clk) control |-> (out == (in0 - in1))
    );

    // The output always matches the operation selected by control.
    check_selected_operation: assert property (
        @(posedge clk) out == (control ? (in0 - in1) : (in0 + in1))
    );

endmodule