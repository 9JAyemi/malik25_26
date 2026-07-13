module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic enable,
    output logic [3:0] out
);
    // Mux output is determined by sel and enable
    mux_output: assert property (
        @(posedge clk) disable iff (!resetn) (out == (sel == 2'b00 ? (enable ? in0 : 4'b0) : 
            sel == 2'b01 ? (enable ? in1 : 4'b0) : 
            sel == 2'b10 ? (enable ? in2 : 4'b0) : 
            sel == 2'b11 ? (enable ? in3 : 4'b0) : 4'b0)))
    );
endmodule