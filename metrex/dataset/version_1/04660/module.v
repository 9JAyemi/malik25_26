module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    input [7:0] d,
    output [3:0] counter_out,
    output [7:0] shift_reg_out,
    output [7:0] final_output
);

    // Circular shift register
    reg [7:0] shift_reg;
    always @(negedge clk) begin
        shift_reg <= {shift_reg[6:0], d};
    end
    assign shift_reg_out = shift_reg;

    // 4-bit binary counter
    reg [3:0] counter;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter <= 4'b1000;
        end else begin
            counter <= counter + 1;
        end
    end
    assign counter_out = counter;

    // Functional module to add shift_reg and counter
    reg [7:0] sum;
    always @(*) begin
        sum = shift_reg + counter;
    end
    assign final_output = sum;

endmodule