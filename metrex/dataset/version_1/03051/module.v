
module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);
    always @(*) begin
        casex(in)  
            8'b00000001: pos = 0;
            8'b00000010: pos = 1;
            8'b00000100: pos = 2;
            8'b00001000: pos = 3;
            8'b00010000: pos = 4;
            8'b00100000: pos = 5;
            8'b01000000: pos = 6;
            8'b10000000: pos = 7;
            default: pos = 3'b111;
        endcase
    end
endmodule
module shift_register (
    input clk,
    input reset,
    input d,
    output reg [3:0] q 
);
    always @(posedge clk or negedge reset) begin
        if (reset == 1'b0) begin
            q <= 4'b0000;
        end else begin
            q <= {q[2:0], d};
        end
    end
endmodule
module functional_module (
    input [2:0] pos,
    input [3:0] shift_reg, 
    output reg out
);
    always @(*) begin
        out = (pos == shift_reg[3:1]); 
    end
endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] in,
    output [2:0] pos,
    input d,
    output reg [3:0] q, 
    output out
);
    priority_encoder pe(in, pos);
    shift_register sr(clk, reset, d, q);
    functional_module fm(pos, q, out); 
endmodule