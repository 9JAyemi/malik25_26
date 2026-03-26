module comparator_4bit (
    input [3:0] in0,
    input [3:0] in1,
    input clk,
    output reg [1:0] out
);

reg [3:0] reg_in0;
reg [3:0] reg_in1;
reg [1:0] reg_out;

always @(posedge clk) begin
    reg_in0 <= in0;
    reg_in1 <= in1;

    if(reg_in0 < reg_in1) begin
        reg_out <= 2'b00;
    end else if(reg_in0 == reg_in1) begin
        reg_out <= 2'b01;
    end else begin
        reg_out <= 2'b10;
    end
end

always @(*) begin
    out = reg_out;
end

endmodule