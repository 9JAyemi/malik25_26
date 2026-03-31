
module gray_counter (
    input clk,
    input reset, // Synchronous active-high reset
    input up_down,
    input enable,
    output reg [1:0] counter_out, // Output from the counter
    output reg [1:0] gray_out // Output from the Gray code converter
);

    always @(posedge clk) begin
        if (reset) begin
            counter_out <= 2'b0;
        end else if (enable) begin
            if (up_down) begin
                counter_out <= counter_out + 2'b1;
            end else begin
                counter_out <= counter_out - 2'b1;
            end
        end
    end

    always @(*) begin
        case (counter_out)
            2'b00: gray_out <= 2'b00;
            2'b01: gray_out <= 2'b01;
            2'b11: gray_out <= 2'b11;
            2'b10: gray_out <= 2'b10;
            default: gray_out <= 2'bx; // Added default case to resolve conflicts
        endcase
    end

endmodule
module functional_module (
    input [1:0] counter_out,
    input [1:0] gray_out,
    output [7:0] q
);

    assign q = {gray_out, counter_out}; // Corrected the order of outputs

endmodule
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input up_down,
    input enable,
    output [7:0] q // 8-bit output from the functional module
);

    wire [1:0] counter_out;
    wire [1:0] gray_out;

    gray_counter counter (
        .clk(clk),
        .reset(reset),
        .up_down(up_down),
        .enable(enable),
        .counter_out(counter_out),
        .gray_out(gray_out)
    );

    functional_module func (
        .counter_out(counter_out),
        .gray_out(gray_out),
        .q(q)
    );

endmodule