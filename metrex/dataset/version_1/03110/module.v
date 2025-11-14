
module bcd_counter_and_gate(
    input clk,
    input reset,   // Synchronous active-high reset
    input a, 
    input b,
    output reg [3:0] ena,
    output reg [15:0] q
);

reg [3:0] count;
wire and_result;
wire [3:0] bcd_out;

// Modulo-10 counter for each digit
always @(posedge clk, posedge reset) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        if (ena[3]) begin
            count[3] <= count[3] + 1;
        end
        if (ena[2]) begin
            count[2] <= count[2] + 1;
        end
        if (ena[1]) begin
            count[1] <= count[1] + 1;
        end
        if (ena[0]) begin
            count[0] <= count[0] + 1;
        end
    end
end

// Combinational circuit to convert binary to BCD
assign bcd_out = {count[3], count[2], count[1], count[0]} + (count[3] >= 5 || count[2] >= 5 || count[1] >= 5 || count[0] >= 5 ? 4'b0110 : 4'b0000);

// AND gate module
and_gate and_gate_inst(
    .a(a),
    .b(b),
    .out(and_result)
);

// Final output module
always @(*) begin
  q = bcd_out & {4{and_result}};
  ena = 4'b1111;
end

endmodule
module and_gate(
    input a,
    input b,
    output out
);

assign out = a & b;

endmodule