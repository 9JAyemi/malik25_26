module pipeline_module( input in, input clk, output reg out );

reg reg1, reg2, reg3;

always @(posedge clk) begin
    reg1 <= in;
end

always @(posedge clk) begin
    reg2 <= reg1;
end

always @(posedge clk) begin
    reg3 <= reg2;
end

always @* begin
    out = reg3;
end

endmodule