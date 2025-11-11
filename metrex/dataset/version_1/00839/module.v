module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    input up_down,    // Control input to select count direction
    input [1:0] input_value, // 2-bit input for the functional module
    output [1:0] output_value, // 2-bit output from the functional module
    output [2:0] counter_output // 3-bit output from the counter
);

reg [2:0] counter;
wire [1:0] sum;
wire carry_out;

// 3-bit binary counter with asynchronous reset
always @(posedge clk or posedge reset) begin
    if (reset) begin
        counter <= 3'b0;
    end else begin
        if (up_down) begin
            counter <= counter + 1;
        end else begin
            counter <= counter - 1;
        end
    end
end

// Functional module that adds the output of the counter and a 2-bit input value using only XOR and AND gates
assign sum[0] = counter[0] ^ input_value[0];
assign sum[1] = (counter[1] ^ input_value[1]) ^ (counter[0] & input_value[0]);
assign carry_out = (counter[1] & input_value[1]) | (counter[0] & input_value[0]);
assign output_value = sum;

// Output signals
assign counter_output = counter;

endmodule