module shift_register (
    input [3:0] in,
    input shift_dir,
    input clk,
    output reg [3:0] out
);
    
    reg [3:0] reg1, reg2, reg3, reg4;
    
    always @(posedge clk) begin
        if (shift_dir == 1) begin
            reg1 <= in;
            reg2 <= reg1;
            reg3 <= reg2;
            reg4 <= reg3;
        end else begin
            reg4 <= reg3;
            reg3 <= reg2;
            reg2 <= reg1;
            reg1 <= in;
        end
    end
    
    initial begin
        out <= 4'b0; // Initializing out
    end
    
    always @* begin
        out = reg4;
    end
endmodule