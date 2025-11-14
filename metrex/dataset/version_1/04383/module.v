module dff_keep_5_new (clk, d, q);
    
    
    
    
    input clk;
    input [4:0] d;
    output [4:0] q;
    reg [4:0] q_reg;
    
    always @(posedge clk) begin
        q_reg <= d;
    end
    
    assign q = q_reg;
endmodule