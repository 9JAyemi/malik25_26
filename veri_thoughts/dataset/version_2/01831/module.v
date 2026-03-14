
module barrel_shifter (
    input [3:0] data,
    input [1:0] shift_amount,
    output reg [3:0] shifted_data
);

always @(*) begin
    case (shift_amount)
        2'b00: shifted_data = data;
        2'b01: shifted_data = {data[2:0], data[3]};
        2'b10: shifted_data = {data[1:0], data[3:2]};
        2'b11: shifted_data = {data[0], data[3:1]};
    endcase
end

endmodule

module up_down_counter (
    input clk,
    input up_down,
    input load,
    input reset,
    output reg [3:0] Q
);

always @(posedge clk) begin
    if (reset) begin
        Q <= 4'b0000;
    end else if (load) begin
        Q <= Q;
    end else if (up_down) begin
        Q <= Q + 1;
    end else begin
        Q <= Q - 1;
    end
end

endmodule

module functional_module (
    input [3:0] shifted_data,
    input [3:0] counter_data,
    output [3:0] sum
);

assign sum = shifted_data + counter_data;

endmodule

module top_module (
    input clk,
    input up_down,
    input load,
    input reset,
    input [3:0] data,
    input [1:0] shift_amount,
    output [3:0] Q
);

wire [3:0] shifted_data;
wire [3:0] counter_data;

barrel_shifter barrel_shifter_inst (
    .data(data),
    .shift_amount(shift_amount),
    .shifted_data(shifted_data)
);

up_down_counter up_down_counter_inst (
    .clk(clk),
    .up_down(up_down),
    .load(load),
    .reset(reset),
    .Q(counter_data)
);

functional_module functional_module_inst (
    .shifted_data(shifted_data),
    .counter_data(counter_data),
    .sum(Q)
);

endmodule
