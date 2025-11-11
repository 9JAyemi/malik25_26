
module barrel_shifter(
    input clk,
    input reset,
    input [15:0] data_in,
    input [4:0] shift_amt,
    input left_enable,
    input right_enable,
    output reg [15:0] data_out
);

always @(posedge clk) begin
    if (reset) begin
        data_out <= 16'b0;
    end else begin
        if (left_enable) begin
            data_out <= data_in << shift_amt;
        end else if (right_enable) begin
            data_out <= data_in >> shift_amt;
        end else begin
            data_out <= data_in;
        end
    end
end

endmodule

module splitter(
    input [15:0] data_in,
    output reg [7:0] lower_nibble,
    output reg [7:0] upper_nibble
);

always @(*) begin
    lower_nibble <= data_in[7:0];
    upper_nibble <= data_in[15:8];
end

endmodule

module xor_module(
    input [7:0] in1,
    input [7:0] in2,
    output reg [7:0] out
);

always @(*) begin
    out = in1 ^ in2;
end

endmodule

module top_module(
    input clk,
    input reset,
    input [15:0] data,
    input [4:0] shift_amt,
    input [1:0] select,
    output [7:0] q
);

wire [15:0] shifted_data;
wire [7:0] lower_nibble;
wire [7:0] upper_nibble;
wire [7:0] xor_output;

barrel_shifter barrel_shifter_inst(.clk(clk), .reset(reset), .data_in(data), .shift_amt(shift_amt), .left_enable(select == 2'b01), .right_enable(select == 2'b10), .data_out(shifted_data));
splitter splitter_inst(.data_in(shifted_data), .lower_nibble(lower_nibble), .upper_nibble(upper_nibble));
xor_module xor_module_inst(.in1(lower_nibble), .in2(upper_nibble), .out(xor_output));

assign q = (select == 2'b00) ? xor_output : ((select == 2'b01) ? lower_nibble : upper_nibble);

endmodule
