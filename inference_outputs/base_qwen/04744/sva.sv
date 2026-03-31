```systemverilog
module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] select,
    output logic [3:0] out
);
    // Mux output should match the selected input
    mux_output: assert property (
        @(posedge clk) disable iff (!resetn) (select == 2'b00) |-> (out == in0)
    );
    mux_output_1: assert property (
        @(posedge clk) disable iff (!resetn) (select == 2'b01) |-> (out == in1)
    );
    mux_output_2: assert property (
        @(posedge clk) disable iff (!resetn) (select == 2'b10) |-> (out == in2)
    );
    mux_output_3: assert property (
        @(posedge clk) disable iff (!resetn) (select == 2'b11) |-> (out == in3)
    );
endmodule
```