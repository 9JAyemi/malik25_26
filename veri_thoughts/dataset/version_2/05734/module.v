module up_down_counter(
    input wire clk,        // Clock input
    input wire reset,      // Reset input
    input wire up_down,    // Control input for up or down counting
    output wire [3:0] out  // Counter output
);

    reg [3:0] counter;

    always @(posedge clk) begin
        if (reset) begin
            counter <= 4'b0000;
        end else begin
            if (up_down) begin
                counter <= counter + 1;
            end else begin
                counter <= counter - 1;
            end
        end
    end

    assign out = counter;

endmodule

module adder(
    input wire [3:0] a,        // First input to the adder
    input wire [3:0] b,        // Second input to the adder
    output wire [3:0] sum      // Sum output
);

    assign sum = a + b;

endmodule

module top_module(
    input wire clk,                // Clock input
    input wire reset,              // Reset input
    input wire up_down,            // Control input for up or down counting
    input wire [3:0] add_value,    // Fixed value to be added to the counter output
    output wire [3:0] out          // Final output, modified counter output
);

    wire [3:0] counter_out;
    wire [3:0] adder_out;

    up_down_counter udc(
        .clk(clk),
        .reset(reset),
        .up_down(up_down),
        .out(counter_out)
    );

    adder add(
        .a(counter_out),
        .b(add_value),
        .sum(adder_out)
    );

    assign out = adder_out;

endmodule