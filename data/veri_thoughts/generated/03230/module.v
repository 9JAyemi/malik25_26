
module shift_register_counter (
    input clk,
    input rst,
    input en,
    input load,
    input [3:0] data_in,
    input sel,
    output [3:0] out
);

reg [3:0] shift_reg;
reg [3:0] counter;

always @(posedge clk) begin
    if (rst) begin
        shift_reg <= 4'b0000;
        counter <= 4'b0000;
    end else if (en) begin
        if (load) begin
            shift_reg <= data_in;
        end else begin
            counter <= counter + 1;
        end
    end
end

assign out = sel ? counter : shift_reg;

endmodule

module adder (
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] sum
);

assign sum = in1 + in2;

endmodule

module top_module (
    input clk,
    input rst,
    input en,
    input load,
    input [3:0] data_in,
    input sel,
    output [3:0] out
);

wire [3:0] shift_reg_out;
wire [3:0] counter_out;
wire [3:0] sum_out;

shift_register_counter shift_counter (
    .clk(clk),
    .rst(rst),
    .en(en),
    .load(load),
    .data_in(data_in),
    .sel(sel),
    .out(shift_reg_out)
);

shift_register_counter counter (
    .clk(clk),
    .rst(rst),
    .en(en),
    .load(1'b0),
    .data_in(4'b0000),
    .sel(sel),
    .out(counter_out)
);

adder sum (
    .in1(shift_reg_out),
    .in2(counter_out),
    .sum(sum_out)
);

assign out = sum_out;

endmodule
