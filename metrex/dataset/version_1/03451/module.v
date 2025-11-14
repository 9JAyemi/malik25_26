module top_module (
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    input [31:0] in,
    output reg [7:0] sum
);

// Rotator module with synchronous load input
reg [99:0] rot_data;
reg [31:0] rot_in;
reg [31:0] rot_out;
reg [4:0] rot_amt;

always @(posedge clk) begin
    if (load) begin
        rot_data <= data;
        rot_in <= in;
        rot_amt <= rot_in[4:0];
    end else if (ena[0]) begin
        rot_data <= {rot_data[99-rot_amt:0], rot_data[99:99-rot_amt]};
    end else if (ena[1]) begin
        rot_data <= {rot_data[99-rot_amt:0], rot_data[99:99-rot_amt]};
        rot_out <= {rot_data[31:24], rot_data[23:16], rot_data[15:8], rot_data[7:0]};
    end
end

// Byte ordering module
reg [31:0] byte_in;
reg [31:0] byte_out;

always @(posedge clk) begin
    if (ena[1]) begin
        byte_in <= rot_out;
        byte_out <= {byte_in[7:0], byte_in[15:8], byte_in[23:16], byte_in[31:24]};
    end
end

// Functional module to calculate sum of bytes
always @(posedge clk) begin
    if (ena[1]) begin
        sum <= byte_out[7:0] + byte_out[15:8] + byte_out[23:16] + byte_out[31:24];
    end
end

endmodule