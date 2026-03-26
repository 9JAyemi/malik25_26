
module program_counter(
    input clk,
    input rst,
    output [5:0] address,
    output [31:0] Inst_code
);

reg [31:0] PC;

always @(posedge clk or posedge rst) begin
    if (rst) begin
        PC <= 32'd0;
    end else begin
        PC <= PC + 32'd4;
    end
end

assign address = PC[7:2];
assign Inst_code = PC;

endmodule
