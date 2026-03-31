```systemverilog
module mux_4to1_enable_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    output logic [3:0] out
);
    // Combinational logic, so use @(posedge clk)
    // Ensure that out is correctly selected based on sel and en
    mux_output: assert property (
        @(posedge clk) disable iff (!en) out == (sel == 2'b00 ? in0 : (sel == 2'b01 ? in1 : (sel == 2'b10 ? in2 : (sel == 2'b11 ? in3 : 4'b0))))
    );
    // Ensure that out is zero when en is zero
    mux_zero_when_en_zero: assert property (
        @(posedge clk) disable iff (!en) out == 4'b0
    );
endmodule
```