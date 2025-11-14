
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

    // Define internal wires and registers
    wire [31:0] adder1_out;
    wire [31:0] adder2_out;
    reg [31:0] selected_out;

    // Instantiate the two ripple carry adders
    ripple_carry_adder adder1(.clk(clk), .a(a), .b(b), .sum(adder1_out));
    ripple_carry_adder adder2(.clk(clk), .a(a), .b(b), .sum(adder2_out));

    // Define control logic to select which adder output to use
    always @ (posedge clk or posedge reset) begin
        if (reset) begin
            selected_out <= 0;
        end else begin
            if (adder1_out > adder2_out) begin
                selected_out <= adder1_out;
            end else begin
                selected_out <= adder2_out;
            end
        end
    end

    // Assign the selected output to the sum output port
    assign sum = selected_out;

endmodule
module ripple_carry_adder (
    input clk,
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

    // Define internal wires and registers
    wire [31:0] carry;
    reg [31:0] sum_reg;

    // Implement the ripple carry adder logic
    assign carry[0] = 1'b0;
    genvar i;
    generate
        for (i = 0; i < 31; i = i + 1) begin
            assign carry[i+1] = (sum_reg[i] + a[i] + b[i]) > 1;
            assign sum[i] = sum_reg[i] ^ a[i] ^ b[i] ^ carry[i];
        end
        assign sum[31] = sum_reg[31] ^ a[31] ^ b[31] ^ carry[31];
    endgenerate

    // Instantiate the register for the sum output
    always @ (posedge clk) begin
        sum_reg <= sum;
    end

endmodule