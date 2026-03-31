```systemverilog
module bitwise_op_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] sel,
    output logic [3:0] out
);
    // Combinational logic, so use @(posedge clk)
    // Ensure that the output is correctly set based on the selection
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (out == (sel == 2'b00 ? A & B :
                                                       sel == 2'b01 ? A | B :
                                                       sel == 2'b10 ? A ^ B :
                                                       sel == 2'b11 ? ~(A ^ B) :
                                                       4'b0))
    );
    // Ensure that the output is not undefined for invalid selection
    invalid_sel: assert property (
        @(posedge clk) disable iff (!reset_n) (sel inside {[2'b00:2'b11]})
    );
endmodule
```