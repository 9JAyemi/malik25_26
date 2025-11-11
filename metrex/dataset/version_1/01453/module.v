module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [2:0] input_data, // 3-bit input data
    input control, // Control signal for the multiplexer
    output reg [2:0] counter_out, // 3-bit output from the counter
    output reg [2:0] xor_out // 3-bit output from the XOR module
);

reg [2:0] counter;

always @(posedge clk) begin
    if (reset) begin
        counter <= 3'b000;
    end
    else if (counter == 3'b111) begin
        counter <= 3'b000;
    end
    else begin
        counter <= counter + 1;
    end
end

always @(posedge clk) begin
    if (reset) begin
        xor_out <= 3'b000;
    end
    else begin
        case (control)
            1'b0: xor_out <= counter ^ input_data;
            1'b1: xor_out <= counter_out ^ input_data;
        endcase
    end
end

always @(posedge clk) begin
    if (reset) begin
        counter_out <= 3'b000;
    end
    else begin
        case (control)
            1'b0: counter_out <= counter;
            1'b1: counter_out <= counter_out;
        endcase
    end
end

endmodule