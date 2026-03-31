```systemverilog
module decoder_2to4_sva (
    input logic [1:0] in,
    output logic out0,
    output logic out1,
    output logic out2,
    output logic out3
);
    // Combinational logic, so use @(posedge clk)
    // Ensure that the outputs are correctly set based on the input
    correct_output: assert property (
        @(posedge clk) disable iff (!reset) (in == 2'b00) |-> (out0 == 1) && (out1 == 0) && (out2 == 0) && (out3 == 0)
    );
    correct_output_1: assert property (
        @(posedge clk) disable iff (!reset) (in == 2'b01) |-> (out0 == 0) && (out1 == 1) && (out2 == 0) && (out3 == 0)
    );
    correct_output_2: assert property (
        @(posedge clk) disable iff (!reset) (in == 2'b10) |-> (out0 == 0) && (out1 == 0) && (out2 == 1) && (out3 == 0)
    );
    correct_output_3: assert property (
        @(posedge clk) disable iff (!reset) (in == 2'b11) |-> (out0 == 0) && (out1 == 0) && (out2 == 0) && (out3 == 1)
    );
    // Ensure that the outputs are not set to 1 for any other input
    invalid_output: assert property (
        @(posedge clk) disable iff (!reset) (in != 2'b00) |-> (out0 == 0)
    );
    invalid_output_1: assert property (
        @(posedge clk) disable iff (!reset) (in != 2'b01) |-> (out1 == 0)
    );
    invalid_output_2: assert property (
        @(posedge clk) disable iff (!reset) (in != 2'b10) |-> (out2 == 0)
    );
    invalid_output_3: assert property (
        @(posedge clk) disable iff (!reset) (in != 2'b11) |-> (out3 == 0)
    );
    // Ensure that the outputs are not set to 1 for any other combination of outputs
    invalid_combination: assert property (
        @(posedge clk) disable iff (!reset) (out0 == 1) && (out1 == 1) && (out2 == 1) && (out3 == 1) |-> 0
    );
endmodule
```