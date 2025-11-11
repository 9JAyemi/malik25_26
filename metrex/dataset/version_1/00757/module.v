module binary_counter_4bit (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [3:0] q // Output of the binary counter
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            q <= 4'b0000;
        end else begin
            q <= q + 1;
        end
    end

endmodule

module binary_counter_loadable (
    input clk,
    input reset,          // Asynchronous active-high reset
    input load,           // Active-high parallel load input
    input [3:0] load_value, // 4-bit load value
    output reg [3:0] q,   // Output of the binary counter
    output reg carry_out  // Carry-out output
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            q <= 4'b0101;
            carry_out <= 0;
        end else if (load) begin
            q <= load_value;
            carry_out <= 0;
        end else if (q == 4'b1111) begin
            carry_out <= 1;
        end else begin
            q <= q + 1;
            carry_out <= 0;
        end
    end

endmodule

module control_logic (
    input select,         // Select input to choose between the two modules
    input [3:0] q1,       // Output from the first module
    input [3:0] q2,       // Output from the second module
    input carry_out,      // Carry-out output from the second module
    output [3:0] q_out,   // Output from the active module
    output led            // LED output controlled by the carry-out output
);

    assign q_out = select ? q2 : q1;
    assign led = carry_out;

endmodule

module top_module (
    input clk,
    input reset,          // Synchronous active-high reset
    input load,           // Active-high parallel load input for the second module
    input [3:0] load_value, // 4-bit load value for the second module
    input select,         // Select input to choose between the two modules
    output [3:0] q_out,   // Output from the active module
    output carry_out,     // Carry-out output from the second module
    output led            // LED output controlled by the carry-out output
);

    wire [3:0] q1;
    wire [3:0] q2;
    wire carry_out;

    binary_counter_4bit counter1 (
        .clk(clk),
        .reset(reset),
        .q(q1)
    );

    binary_counter_loadable counter2 (
        .clk(clk),
        .reset(reset),
        .load(load),
        .load_value(load_value),
        .q(q2),
        .carry_out(carry_out)
    );

    control_logic control (
        .select(select),
        .q1(q1),
        .q2(q2),
        .carry_out(carry_out),
        .q_out(q_out),
        .led(led)
    );

endmodule