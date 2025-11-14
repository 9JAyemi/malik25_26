
module multiplier(
    input clk,
    input rst,
    input [7:0] in1,
    input [7:0] in2,
    input [2:0] select,
    output reg [15:0] out
);

wire [7:0] shifted_in2;
reg [15:0] product;

reg [7:0] temp_in2;

assign shifted_in2 = temp_in2 << select;

barrel_shifter barrel_shifter_inst( // instantiated the barrel shifter module
    .in(in2),
    .select(select),
    .shifted_out(temp_in2)
);

always @(posedge clk) begin
    if (rst) begin
        out <= 16'b0;
    end else begin
        if (in1 != in1_prev || in2 != in2_prev) begin
            product <= in1 * shifted_in2; // calculated the product
            out <= product;
        end
    end
end

reg [7:0] in1_prev;
reg [7:0] in2_prev;

always @(posedge clk) begin
    in1_prev <= in1;
    in2_prev <= in2;
end

endmodule
module barrel_shifter(
    input [7:0] in,
    output reg [7:0] shifted_out,
    input [2:0] select
);

always @(*) begin
    case (select)
        3'b000: shifted_out = in;
        3'b001: shifted_out = {in[6:0], 1'b0};
        3'b010: shifted_out = {in[5:0], 2'b00};
        3'b011: shifted_out = {in[4:0], 3'b000};
        3'b100: shifted_out = {in[3:0], 4'b0000};
        3'b101: shifted_out = {in[2:0], 5'b00000};
        3'b110: shifted_out = {in[1:0], 6'b000000};
        3'b111: shifted_out = {in[0], 7'b0000000};
    endcase
end

endmodule