module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

reg [31:0] in_reg1, in_reg2, in_reg3, in_reg4;
reg [31:0] out_reg1, out_reg2, out_reg3, out_reg4;

always @(posedge clk or negedge reset) begin
    if (reset == 0) begin
        in_reg1 <= 0;
        in_reg2 <= 0;
        in_reg3 <= 0;
        in_reg4 <= 0;
        out_reg1 <= 0;
        out_reg2 <= 0;
        out_reg3 <= 0;
        out_reg4 <= 0;
    end
    else begin
        in_reg1 <= in;
        in_reg2 <= in_reg1;
        in_reg3 <= in_reg2;
        in_reg4 <= in_reg3;
        
        if (in_reg4 == 32'hFFFFFFFF) begin
            out_reg1 <= 0;
            out_reg2 <= 0;
            out_reg3 <= 0;
            out_reg4 <= 0;
        end
        else if (in_reg4 == 32'hFFFFFFFE) begin
            out_reg1 <= 1;
            out_reg2 <= 1;
            out_reg3 <= 1;
            out_reg4 <= 1;
        end
        else begin
            out_reg1 <= out_reg2;
            out_reg2 <= out_reg3;
            out_reg3 <= out_reg4;
            out_reg4 <= 0;
        end
    end
end

assign out = out_reg1;

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

transition_detector td (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out)
);

endmodule