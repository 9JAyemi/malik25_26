
module top_module (
    input               clk         ,
    input               rst_n       ,
    input       [7:0]   data_in_1   ,
    input       [7:0]   data_in_2   ,
    input               valid_a     ,
    input               ready_b     ,
    output              ready_a     ,
    output              valid_b     ,
    output      [8:0]   data_out
);

wire [8:0] sum;
wire carry;

 adder8 adder_inst (
    .a(data_in_1),
    .b(data_in_2),
    .sum(sum)
);

assign carry = (data_in_1+data_in_2) > 255 ? 1'b1 : 1'b0;

reg [8:0] sum2;
reg [8:0] data_out_r;
reg valid_b_r;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        sum2 <= 0;
        data_out_r <= 0;
        valid_b_r <= 0;
    end else begin
        sum2 <= sum + sum2;
        data_out_r <= sum;
        valid_b_r <= valid_a;
    end
end

assign data_out = data_out_r;
assign valid_b = valid_b_r;
assign ready_a = !valid_b || ready_b;

endmodule
module adder8 (
    input       [7:0]   a           ,
    input       [7:0]   b           ,
    output reg  [8:0]   sum
);

always @(*) begin
    sum = a + b;
end

endmodule
module carry_out (
    input       [7:0]   a           ,
    input       [7:0]   b           ,
    output reg          cout
);

always @(*) begin
    cout = (a+b) > 255 ? 1'b1 : 1'b0;
end

endmodule