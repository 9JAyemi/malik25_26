module Adder4bit_assertions (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] S,
    output logic Co
);
    // RippleCarryAdder4bit should not drive Co when Ci is 1'b0
    ripple_carry_adder_co: assert property (
        @(posedge CLK) disable iff (!CLK) (Ci == 1'b0) |-> (Co == 1'b0)
    );

    // RippleCarryAdder4bit should correctly compute the sum S
    ripple_carry_adder_sum: assert property (
        @(posedge CLK) disable iff (!CLK) (Ci == 1'b0) |-> (S == A + B)
    );

    // FullAdder should not drive Co when Ci is 1'b0
    full_adder_co: assert property (
        @(posedge CLK) disable iff (!CLK) (Ci == 1'b0) |-> (Co == 1'b0)
    );

    // FullAdder should correctly compute the sum S
    full_adder_sum: assert property (
        @(posedge CLK) disable iff (!CLK) (Ci == 1'b0) |-> (S == A + B)
    );

    // Mux1 should correctly select between A and B based on Sel
    mux1_output: assert property (
        @(posedge CLK) disable iff (!CLK) |-> (Out == (Sel ? A : B))
    );

    // Mux4bit should correctly select between A and B based on Sel
    mux4bit_output: assert property (
        @(posedge CLK) disable iff (!CLK) |-> (Out == (Sel ? A : B))
    );
endmodule