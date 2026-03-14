
module top_module (
    input clk,
    input reset,
    input up_down,
    input [7:0] in_hi,
    input [7:0] in_lo,
    output [15:0] out
);

wire [2:0] count;
wire [15:0] hw;
wire [15:0] final_out;

// Instantiate the 3-bit binary counter module
counter_3bit counter_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .count(count)
);

// Instantiate the combinational circuit module
combinational_circuit comb_inst (
    .in_hi(in_hi),
    .in_lo(in_lo),
    .out(hw)
);

// Instantiate the functional module
functional_module func_inst (
    .hw(hw),
    .count(count),
    .out(final_out)
);

// Assign the final output to the output port
assign out = final_out;

endmodule

module counter_3bit (
    input clk,
    input reset,
    input up_down,
    output reg [2:0] count
);

always @(posedge clk) begin
    if (reset == 0) begin
        count <= 3'b000;
    end else if (up_down == 1) begin
        count <= count + 1;
    end else begin
        count <= count - 1;
    end
end

endmodule

module combinational_circuit (
    input [7:0] in_hi,
    input [7:0] in_lo,
    output reg [15:0] out
);

always @* begin
    out = {in_hi, in_lo};
end

endmodule

module functional_module (
    input [15:0] hw,
    input [2:0] count,
    output reg [15:0] out
);

always @(*) begin
    out = hw + count;
end

endmodule
