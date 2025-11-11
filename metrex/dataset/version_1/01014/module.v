
module multiplier_4bit (
    input clk,
    input [3:0] A,
    input [3:0] B,
    output [7:0] S
);

reg [7:0] reg_file [0:15]; // Register file with 16 registers

// Fetch stage
reg [3:0] addr1, addr2;
always @ (posedge clk) begin
    addr1 <= A;
    addr2 <= B;
end

// Execute stage
reg [7:0] data1, data2;
reg [15:0] result;
always @ (posedge clk) begin
    data1 <= reg_file[addr1];
    data2 <= reg_file[addr2];
    result <= data1 * data2;
end

// Write back stage
always @ (posedge clk) begin
    reg_file[addr1] <= result[7:0];
    reg_file[addr2] <= result[15:8];
end

// Output stage
assign S = reg_file[addr1]; // Output is the result in the first register

endmodule
