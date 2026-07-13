
module binary_counter(clk, en, clr, count);
    input clk, en, clr;
    output reg [3:0] count;

    always @(posedge clk) begin
        if(clr == 1'b1) begin
            count <= 4'b0;
        end
        else if(en == 1'b1) begin
            count <= count + 4'b1;
        end
    end
endmodule

