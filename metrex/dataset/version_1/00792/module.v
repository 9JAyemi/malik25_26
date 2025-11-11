
module signed_mag_comp (
    input signed [3:0] A,
    input signed [3:0] B,
    input clk,  // Added clock input
    output reg C
);

reg [3:0] A_abs, B_abs;
reg [3:0] A_sign, B_sign;
reg [3:0] A_mag, B_mag;

wire [3:0] A_mag_reg, B_mag_reg;
wire [3:0] A_sign_reg, B_sign_reg;
wire [3:0] A_abs_reg, B_abs_reg;

assign A_mag_reg = A_mag;
assign B_mag_reg = B_mag;
assign A_sign_reg = A_sign;
assign B_sign_reg = B_sign;
assign A_abs_reg = A_abs;
assign B_abs_reg = B_abs;

// Pipeline Stage 1: Absolute Value Calculation
always @(*) begin
    if (A[3] == 1'b1) begin
        A_abs = ~A + 1;
    end else begin
        A_abs = A;
    end
    
    if (B[3] == 1'b1) begin
        B_abs = ~B + 1;
    end else begin
        B_abs = B;
    end
end

// Pipeline Stage 2: Sign Calculation
always @(*) begin
    if (A[3] == 1'b1) begin
        A_sign = 1'b1;
    end else begin
        A_sign = 1'b0;
    end
    
    if (B[3] == 1'b1) begin
        B_sign = 1'b1;
    end else begin
        B_sign = 1'b0;
    end
end

// Pipeline Stage 3: Magnitude Calculation
always @(*) begin
    if (A_abs > B_abs) begin
        A_mag = A_abs;
        B_mag = B_abs;
    end else begin
        A_mag = B_abs;
        B_mag = A_abs;
    end
end

// Pipeline Stage 4: Comparison
always @(posedge clk) begin  // Changed from always @(*) to always @(posedge clk)
    if (A_mag_reg >= B_mag_reg) begin
        C <= 1'b1;
    end else begin
        C <= 1'b0;
    end
end

endmodule
