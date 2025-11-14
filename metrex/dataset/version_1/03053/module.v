
module module1 (
    input clk,
    input reset,
    input [7:0] d,
    output [7:0] q1
);

// Register for storing the input data
reg [7:0] d_r;

// Register for storing the output data
reg [7:0] q1_r;

// Register for storing the reversed output data
reg [7:0] q1_reversed;

always @(negedge clk) begin
    // Trigger the control logic module on the negative edge of clk
    if (reset) begin
        d_r <= 8'b0;
        q1_r <= 8'b0;
        q1_reversed <= 8'b0;
    end else begin
        d_r <= d;
        q1_r <= {q1_r[6], q1_r[5], q1_r[4], q1_r[3], q1_r[2], q1_r[1], q1_r[0], d_r[7]};
        q1_reversed <= {q1_r[7], q1_r[6], q1_r[5], q1_r[4], q1_r[3], q1_r[2], q1_r[1], q1_r[0]};
    end
end

// Output the reversed output data
assign q1 = q1_reversed;

endmodule

module module2 (
    input clk,
    input reset,
    input [7:0] in,
    output [7:0] q2
);

// Register for storing the input data
reg [7:0] in_r;

// Register for storing the output data
reg [7:0] q2_r;

always @(negedge clk) begin
    // Trigger the control logic module on the negative edge of clk
    if (reset) begin
        in_r <= 8'b0;
        q2_r <= 8'b0;
    end else begin
        in_r <= in;
        q2_r <= {q2_r[6], q2_r[5], q2_r[4], q2_r[3], q2_r[2], q2_r[1], q2_r[0], in_r[7]};
    end
end

// Output the output data
assign q2 = q2_r;

endmodule
