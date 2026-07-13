
module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input ena,     // Synchronous active-high enable
    input [1023:0] in,
    input [7:0] sel,
    output [7:0] out);

    reg [15:0] counter;
    reg [7:0] mux_output;
    wire [3:0] select_input;
    wire [11:0] add_output;

    // 4-digit binary up-counter
    always @(posedge clk) begin
        if (reset) begin
            counter <= 0;
        end else if (ena) begin
            counter <= counter + 1;
        end
    end

    // 256-to-1 multiplexer with priority encoder
    assign select_input = 1 <<< sel[2:0];

    always @(*) begin
        mux_output = in[select_input * 4 +: 4];
    end

    // Additive functional module
    assign add_output = counter + mux_output;

    assign out = add_output[11:4];

endmodule