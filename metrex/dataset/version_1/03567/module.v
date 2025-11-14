module add_sub (
    input [3:0] a,
    input [3:0] b,
    input sub, // 0 for addition, 1 for subtraction
    input cin, // carry in
    output reg cout, // carry out
    output reg overflow, // overflow flag
    output reg [3:0] sum // sum result
);

reg [3:0] a_reg, b_reg; // Register to hold input values
reg sub_reg, cin_reg; // Register to hold sub and cin signals

// Wires to connect adders
wire [4:0] add_out;
wire [3:0] sub_out;

// Instantiate adders
assign add_out = a_reg + b_reg + cin_reg; // Adder for addition
assign sub_out = a_reg - b_reg - cin_reg; // Subtractor for subtraction

// Always block to update registers
always @(*) begin
    a_reg <= a; // Register input a
    b_reg <= b; // Register input b
    sub_reg <= sub; // Register sub signal
    cin_reg <= cin; // Register cin signal
end

// Always block to calculate sum and overflow
always @(*) begin
    if (sub_reg) begin // If subtraction is selected
        sum <= sub_out; // Store subtraction result in sum register
    end else begin // If addition is selected
        sum <= add_out; // Store addition result in sum register
    end

    // Check for overflow
    if (sum > 4'b1111 || sum < 4'b0000) begin
        overflow <= 1; // Set overflow flag
    end else begin
        overflow <= 0; // Clear overflow flag
    end
end

// Always block to calculate carry out
always @(*) begin
    // Check for carry out
    if (sum > 4'b1111 || sum < 4'b0000) begin
        cout <= 1; // Set carry out
    end else begin
        cout <= add_out[4]; // Carry out is the MSB of addition result
    end
end

endmodule