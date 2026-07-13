
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] SUM,
    output CARRY
);

reg [3:0] temp_SUM;
wire [3:0] temp_CARRY;

// Stage 1
always @ (*) begin
    {temp_CARRY[0], temp_SUM[0]} = A[0] + B[0];
end

// Stage 2
always @ (*) begin
    {temp_CARRY[1], temp_SUM[1]} = A[1] + B[1] + temp_CARRY[0];
end

// Stage 3
always @ (*) begin
    {temp_CARRY[2], temp_SUM[2]} = A[2] + B[2] + temp_CARRY[1];
end

// Stage 4
always @ (*) begin
    {CARRY, temp_SUM[3]} = A[3] + B[3] + temp_CARRY[2];
end

assign SUM = temp_SUM;

endmodule