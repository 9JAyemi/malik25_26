
module shift_register (
    input clk,
    input load,
    input [3:0] in,
    output [3:0] out,
    output [3:0] out_next
);
    
    reg [3:0] stage1, stage2, stage3, stage4;
    
    always @(posedge clk) begin
        if (load) begin
            stage1 <= in;
        end else begin
            stage1 <= stage2;
        end
        
        stage2 <= stage3;
        stage3 <= stage4;
        stage4 <= out_next;
    end
    
    assign out = stage1;
    assign out_next = stage2;
    
endmodule
