
module shift_register_counter (
    input clk,
    input reset,      // Synchronous active-high reset
    input areset,     // Async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    output wire [3:0] shift_out,
    output wire [3:0] counter_out
);

    // Shift register
    reg [3:0] shift_reg;
    always @(posedge clk, negedge areset) begin
        if (!areset) begin
            shift_reg <= 4'b0000;
        end else if (load) begin
            shift_reg <= data;
        end else if (ena) begin
            shift_reg <= {shift_reg[2:0], shift_reg[3]};
        end
    end
    assign shift_out = shift_reg;

    // Counter
    reg [3:0] count;
    always @(posedge clk, negedge reset) begin
        if (!reset) begin
            count <= 4'b0000;
        end else begin
            count <= count + 1;
        end
    end
    assign counter_out = count;

    // Output
    assign shift_out = shift_reg;
    assign counter_out = count;

endmodule