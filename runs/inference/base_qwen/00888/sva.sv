module top_module_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] in4,
    output logic [3:0] out_and,
    output logic [3:0] out_or,
    output logic [3:0] out_xor
);
    // Combinational logic, so use @(posedge clk)
    // Ensure that the outputs are correctly assigned based on the inputs
    output_assignment_and: assert property (
        @(posedge clk) disable iff (!reset_n) (out_and == (in1 & in2 & in3 & in4))
    );
    output_assignment_or: assert property (
        @(posedge clk) disable iff (!reset_n) (out_or == (in1 | in2 | in3 | in4))
    );
    output_assignment_xor: assert property (
        @(posedge clk) disable iff (!reset_n) (out_xor == (in1 ^ in2 ^ in3 ^ in4))
    );
endmodule