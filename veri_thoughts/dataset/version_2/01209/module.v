
module binary_counter (
    input clk,
    input reset,
    output reg [3:0] counter_out
);

always @(posedge clk) begin
    if (reset) begin
        counter_out <= 4'b0000;
    end else begin
        counter_out <= counter_out + 1;
    end
end

endmodule

module shift_register (
    input clk,
    input reset,
    input shift_in,
    output reg [2:0] shift_out
);

always @(posedge clk) begin
    if (reset) begin
        shift_out <= 3'b000;
    end else begin
        shift_out <= {shift_out[1:0], shift_in};
    end
end

endmodule

module functional_module (
    input [3:0] counter_out,
    input [2:0] shift_out,
    output [3:0] final_output
);

assign final_output = counter_out + shift_out[2];

endmodule

module top_module (
    input clk,
    input reset,
    output [3:0] final_output
);

wire [3:0] counter_out;
wire [2:0] shift_out;

binary_counter counter_inst (
    .clk(clk),
    .reset(reset),
    .counter_out(counter_out)
);

shift_register shift_inst (
    .clk(clk),
    .reset(reset),
    .shift_in(counter_out[0]),
    .shift_out(shift_out)
);

functional_module func_inst (
    .counter_out(counter_out),
    .shift_out(shift_out),
    .final_output(final_output)
);

endmodule
