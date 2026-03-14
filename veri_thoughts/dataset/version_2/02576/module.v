module and_nor (
    input a,
    input b,
    output y
);
    wire not_a, not_b;
    nor n1(not_a, a, a);
    nor n2(not_b, b, b);
    nor n3(y, not_a, not_b);
endmodule

module top_module ( 
    input a, 
    input b, 
    input [2:0] sel, 
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input clk,
    output reg [3:0] out
);
    wire [3:0] and_out;
    and_nor and_gate(a, b, and_out[0]);
    
    reg [3:0] mux_out;
    always @(*) begin
        case(sel)
            3'b000: mux_out = data0;
            3'b001: mux_out = data1;
            3'b010: mux_out = data2;
            3'b011: mux_out = data3;
            3'b100: mux_out = data4;
            3'b101: mux_out = data5;
            default: mux_out = 4'b0001;
        endcase
    end
    
    reg [3:0] twos_comp_out;
    always @(*) begin
        if(and_out[0] == 1) begin
            twos_comp_out = ~mux_out + 4'b1;
        end else begin
            twos_comp_out = mux_out;
        end
    end
    
    always @(posedge clk) begin
        out <= twos_comp_out;
    end
    
endmodule