```systemverilog
module four_to_one_sva (
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    output logic output1
);
    // Combinational logic: output1 is HIGH if any of input1, input2, input3, or input4 is HIGH
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (output1 == (input1 | input2 | input3 | input4))
    );
endmodule
```