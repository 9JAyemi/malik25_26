```systemverilog
module top_module_sva (
    input logic clk,
    input logic [2:0] sel, 
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    output logic [3:0] out_mux,
    output logic [2:0] out_3bit,
    output logic o2,
    output logic o1,
    output logic o0,
    output logic [6:0] final_out
);
    // 6-to-1 Multiplexer
    // Mux output should match the selected input data
    mux_output: assert property (
        @(posedge clk) disable iff (!clk) (out_mux == (sel == 0) ? data0 :
                                           (sel == 1) ? data1 :
                                           (sel == 2) ? data2 :
                                           (sel == 3) ? data3 :
                                           (sel == 4) ? data4 :
                                           (sel == 5) ? data5 : 4'b0)
    );

    // 3-bit Input Module
    // out_3bit should match the selected input
    out_3bit_output: assert property (
        @(posedge clk) disable iff (!clk) (out_3bit == sel)
    );

    // out_3bit outputs should match individual bits of sel
    out_3bit_o2: assert property (
        @(posedge clk) disable iff (!clk) (o2 == sel[2])
    );
    out_3bit_o1: assert property (
        @(posedge clk) disable iff (!clk) (o1 == sel[1])
    );
    out_3bit_o0: assert property (
        @(posedge clk) disable iff (!clk) (o0 == sel[0])
    );

    // Functional Module
    // final_out should match the sum of mux_out and sel
    functional_output: assert property (
        @(posedge clk) disable iff (!clk) (final_out == {carry_out, add_out})
    );

    // Adder output should match the sum of mux_out and sel
    adder_output: assert property (
        @(posedge clk) disable iff (!clk) (add_out == mux_out + sel)
    );

    // Carry output should be 0 as there is no carry in the addition
    carry_output: assert property (
        @(posedge clk) disable iff (!clk) (carry_out == 1'b0)
    );
endmodule
```