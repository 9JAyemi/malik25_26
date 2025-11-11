module AdlerChecksum #(
    parameter n = 16 // number of 8-bit data signals
)(
    input [n*8-1:0] data_in,
    input [15:0] checksum,
    output reg [15:0] checksum_result,
    output reg data_valid,       // Signal to indicate valid data
    output reg error_detected,   // Signal to indicate an error (checksum mismatch)
    input clk
);

reg [7:0] A;
reg [7:0] B;
integer i;

always @(posedge clk) begin
    A <= 1;  // Initialize A to 1 at every clock cycle start
    B <= 1;  // Initialize B to 1 at every clock cycle start
    for (i = 0; i < n; i = i + 1) begin
        A <= (A + data_in[i*8 +: 8]) % 251;  // Modular addition in Adler-32 algorithm
        B <= (B + A) % 251;                  // Modular addition in Adler-32 algorithm
    end
    checksum_result <= (B << 8) | A;  // Combine B and A to form the checksum
end

// Logic to handle valid and invalid data
always @(posedge clk) begin
    if (checksum_result == checksum) begin
        // Checksum matches, data is valid
        data_valid <= 1'b1;
        error_detected <= 1'b0; // No error detected
    end else begin
        // Checksum does not match, data is invalid
        data_valid <= 1'b0;
        error_detected <= 1'b1; // Error detected
    end
end

endmodule
