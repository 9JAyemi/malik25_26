module top_module (
    input clk,
    input [7:0] data_in,
    output reg [8:0] out
);

reg [7:0] serial_data;
reg [3:0] parity_bits;

// Parallel to Serial Conversion Module
always @(posedge clk) begin
    serial_data <= data_in;
end

// Hamming Code Parity Generator Module
always @(posedge clk) begin
    parity_bits[0] <= serial_data[0] ^ serial_data[1] ^ serial_data[3] ^ serial_data[4] ^ serial_data[6];
    parity_bits[1] <= serial_data[0] ^ serial_data[2] ^ serial_data[3] ^ serial_data[5] ^ serial_data[6];
    parity_bits[2] <= serial_data[1] ^ serial_data[2] ^ serial_data[3] ^ serial_data[7];
    parity_bits[3] <= serial_data[4] ^ serial_data[5] ^ serial_data[6] ^ serial_data[7];
end

// Output Module
always @(posedge clk) begin
    out[0] <= parity_bits[0];
    out[1] <= parity_bits[1];
    out[2] <= serial_data[0];
    out[3] <= parity_bits[2];
    out[4] <= serial_data[1];
    out[5] <= serial_data[2];
    out[6] <= serial_data[3];
    out[7] <= parity_bits[3];
    out[8] <= serial_data[4];
end

endmodule