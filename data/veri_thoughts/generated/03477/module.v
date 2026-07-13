module TCMP(clk, rst, a, ld, s);
    input clk, rst;
    input a;
    input ld;
    output reg s;
    
    reg z;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            //Reset logic goes here.
            s <= 1'b0;
            z <= 1'b0;
        end
        else  if (ld) begin              // idle state reset before each input word
            s  <= 1'b0;
            z  <= 1'b0;
        end
        else begin
            //Sequential logic goes here.
            z <= a | z;
            s <= a ^ z;
        end
    end
endmodule