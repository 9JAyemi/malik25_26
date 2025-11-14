module regfile (
    input [31:0] wr_data,
    input wr_en,
    input [2:0] wr_addr,
    input [2:0] rd_addr,
    input clk,
    output reg [31:0] rd_data,
    output [1:0] rd_guards ,
    output [1:0] rd_guardsok 
);

reg [31:0] registers [0:7];

always @ (posedge clk) begin
    if (wr_en) begin
        registers[wr_addr] <= wr_data;
    end
end

always @ (*) begin
    rd_data = registers[rd_addr];
end

assign rd_guards = {rd_data[0], 1'b1};

assign rd_guardsok[0] = 1'b1;
assign rd_guardsok[1] = rd_data[0];

endmodule