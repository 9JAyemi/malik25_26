```systemverilog
module binary_converter_sva (
    input logic [9:0] input_val,
    output logic [3:0] binary_val
);
    // Combinational logic, so use @(posedge clk)
    // Convert input_val to binary_val
    convert_to_binary: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000000) |-> (binary_val == 4'b0000)
    );
    convert_to_binary_1: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000001) |-> (binary_val == 4'b0001)
    );
    convert_to_binary_2: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000010) |-> (binary_val == 4'b0010)
    );
    convert_to_binary_3: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000011) |-> (binary_val == 4'b0011)
    );
    convert_to_binary_4: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000100) |-> (binary_val == 4'b0100)
    );
    convert_to_binary_5: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000101) |-> (binary_val == 4'b0101)
    );
    convert_to_binary_6: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000110) |-> (binary_val == 4'b0110)
    );
    convert_to_binary_7: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000000111) |-> (binary_val == 4'b0111)
    );
    convert_to_binary_8: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000001000) |-> (binary_val == 4'b1000)
    );
    convert_to_binary_9: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val == 10'b0000001001) |-> (binary_val == 4'b1001)
    );
    convert_to_binary_default: assert property (
        @(posedge clk) disable iff (!reset_n) (input_val != 10'b0000000000 && input_val != 10'b0000000001 && input_val != 10'b0000000010 && input_val != 10'b0000000011 && input_val != 10'b0000000100 && input_val != 10'b0000000101 && input_val != 10'b0000000110 && input_val != 10'b0000000111 && input_val != 10'b0000001000 && input_val != 10'b0000001001) |-> (binary_val == 4'b0000)
    );
endmodule
```