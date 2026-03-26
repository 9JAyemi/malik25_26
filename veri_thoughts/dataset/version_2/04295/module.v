module parallel_load_shift (
    input [7:0] data_in,
    input [2:0] shift_amount,
    output [7:0] data_out,
    input clk
);

reg [7:0] reg1, reg2, reg3, reg4;
wire [7:0] shifted_reg1, shifted_reg2, shifted_reg3;

always @(posedge clk) begin
    reg1 <= data_in;
    reg2 <= reg1;
    reg3 <= reg2;
    reg4 <= reg3;
end

assign shifted_reg1 = reg1 >> shift_amount[2];
assign shifted_reg2 = reg2 >> shift_amount[1];
assign shifted_reg3 = reg3 >> shift_amount[0];
assign data_out = {shifted_reg3, shifted_reg2, shifted_reg1};

endmodule