module up_down_counter (
    input clk,
    input up_down,
    input load,
    input [3:0] binary,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (load) begin
        count <= binary;
    end else if (up_down) begin
        count <= count + 1;
    end else begin
        count <= count - 1;
    end
end

endmodule

module binary_to_bcd_converter (
    input [3:0] binary,
    output [3:0] BCD_HIGH,
    output [3:0] BCD_LOW
);

assign BCD_HIGH = binary / 10;
assign BCD_LOW = binary % 10;

endmodule

module top_module (
    input clk,
    input up_down,
    input load,
    input [3:0] binary,
    output [3:0] BCD_HIGH,
    output [3:0] BCD_LOW
);

wire [3:0] count;
up_down_counter counter(.clk(clk), .up_down(up_down), .load(load), .binary(binary), .count(count));
binary_to_bcd_converter converter(.binary(count), .BCD_HIGH(BCD_HIGH), .BCD_LOW(BCD_LOW));

endmodule