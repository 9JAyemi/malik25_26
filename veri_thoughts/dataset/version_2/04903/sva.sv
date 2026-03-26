module logic_circuit_sva (
    input logic       clk,
    input logic [1:0] in1,
    input logic [1:0] in2,
    input logic [1:0] out
);

    // Sample the combinational NAND relation on clk; RTL has no reset.
    check_out_matches_nand: assert property (
        @(posedge clk) disable iff (1'b0) out == ~(in1 & in2)
    );

    // Bit 0 must implement a NAND of in1[0] and in2[0].
    check_out0_matches_nand: assert property (
        @(posedge clk) disable iff (1'b0) out[0] == ~(in1[0] & in2[0])
    );

    // Bit 1 must implement a NAND of in1[1] and in2[1].
    check_out1_matches_nand: assert property (
        @(posedge clk) disable iff (1'b0) out[1] == ~(in1[1] & in2[1])
    );

    // If either bit-0 input is 0, bit-0 output must be 1.
    check_out0_high_when_any_input_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in1[0] == 1'b0) || (in2[0] == 1'b0)) |-> (out[0] == 1'b1)
    );

    // If both bit-0 inputs are 1, bit-0 output must be 0.
    check_out0_low_when_both_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in1[0] == 1'b1) && (in2[0] == 1'b1)) |-> (out[0] == 1'b0)
    );

    // If either bit-1 input is 0, bit-1 output must be 1.
    check_out1_high_when_any_input_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in1[1] == 1'b0) || (in2[1] == 1'b0)) |-> (out[1] == 1'b1)
    );

    // If both bit-1 inputs are 1, bit-1 output must be 0.
    check_out1_low_when_both_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in1[1] == 1'b1) && (in2[1] == 1'b1)) |-> (out[1] == 1'b0)
    );

    // Stable inputs must produce a stable output.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(in1) && $stable(in2)) |-> $stable(out)
    );

endmodule